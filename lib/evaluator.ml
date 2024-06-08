open! Core
open Typed_tree

module Ctx = struct
  type t = some_v Id.Table.t

  let create = Id.Table.create
  let set ctx ~name ~value = Hashtbl.set ctx ~key:name ~data:value
  let find_exn = Hashtbl.find_exn
end

let rec eval : type a. Ctx.t -> (a data_ty, det) texp -> a =
 fun ctx { ty = Data ty; exp } ->
  match exp with
  | Value v -> v
  | RVar x -> (
      let (Ex (tv, v)) = Ctx.find_exn ctx x in
      match (ty, tv) with
      | Tyu, Tyu -> v
      | Tyi, Tyi -> v
      | Tyr, Tyr -> v
      | Tyb, Tyb -> v
      | _ -> assert false)
  | Bop (op, te1, te2) -> op.f (eval ctx te1) (eval ctx te2)
  | Uop (op, te) -> op.f (eval ctx te)
  | If (te_pred, te_cons, te_alt) ->
      if eval ctx te_pred then eval ctx te_cons else eval ctx te_alt

let rec sample : type a. Ctx.t -> (a dist_ty, det) texp -> a =
 fun ctx { exp; _ } ->
  match exp with
  | If (te_pred, te_cons, te_alt) ->
      if eval ctx te_pred then sample ctx te_cons else sample ctx te_alt
  | Call (f, args) -> f.sampler (eval_args ctx args)

and eval_args : type a. Ctx.t -> (a, det) args -> a vargs =
 fun ctx -> function
  | [] -> []
  | ({ ty = Data ty; _ } as te) :: tl -> (ty, eval ctx te) :: eval_args ctx tl

let rec eval_pmdf : type a. Ctx.t -> (a dist_ty, det) texp -> some_v -> float =
 fun ctx { ty = Dist ty; exp } ->
  match exp with
  | If (te_pred, te_cons, te_alt) ->
      if eval ctx te_pred then eval_pmdf ctx te_cons else eval_pmdf ctx te_alt
  | Call (f, args) ->
      let pmdf (Ex (ty', v) : some_v) =
        match (ty, ty') with
        | Tyu, Tyu -> f.log_pmdf (eval_args ctx args) v
        | Tyi, Tyi -> f.log_pmdf (eval_args ctx args) v
        | Tyr, Tyr -> f.log_pmdf (eval_args ctx args) v
        | Tyb, Tyb -> f.log_pmdf (eval_args ctx args) v
        | _, _ -> assert false
      in
      pmdf

let gibbs_sampling ~(num_samples : int) (graph : Graph.t) (query : some_det) :
    float array =
  (* Initialize the context with the observed values. Float conversion must
     succeed as observed variables do not contain free variables *)
  let default : type a. a ty -> a = function
    | Tyu -> ()
    | Tyi -> 0
    | Tyr -> 0.0
    | Tyb -> false
  in
  let ctx = Id.Table.create () in
  Map.iteri graph.obs_map ~f:(fun ~key:name ~data:value ->
      Ctx.set ctx ~name ~value);

  let unobserved = Graph.unobserved_vertices_pmdfs graph in
  List.iter unobserved ~f:(fun (name, Ex { ty = Dist ty; _ }) ->
      let value : some_v = Ex (ty, default ty) in
      Ctx.set ctx ~name ~value);

  (* Adapted from gibbs_sampling of Owl *)
  let a, b = (1000, 10) in
  let num_iter = a + (b * num_samples) in
  let samples = Array.create ~len:num_samples 0. in
  for i = 0 to num_iter - 1 do
    (* Gibbs step *)
    List.iter unobserved ~f:(fun (name, Ex { ty = Dist ty; exp }) ->
        let curr = Ctx.find_exn ctx name in
        let log_pmdf = eval_pmdf ctx { ty = Dist ty; exp } in
        let cand : some_v = Ex (ty, sample ctx { ty = Dist ty; exp }) in

        (* metropolis-hastings update logic *)
        Ctx.set ctx ~name ~value:cand;
        let log_pmdf' = eval_pmdf ctx { ty = Dist ty; exp } in
        let log_alpha = log_pmdf' curr -. log_pmdf cand in

        (* variables influenced by "name" *)
        let name_infl =
          Map.filteri graph.pmdf_map ~f:(fun ~key:name' ~data:(Ex { exp; _ }) ->
              Id.(name' = name) || Set.mem (fv exp) name)
        in
        let log_alpha =
          Map.fold name_infl ~init:log_alpha
            ~f:(fun ~key:name' ~data:(Ex exp) acc ->
              let prob_w_cand = (eval_pmdf ctx exp) (Ctx.find_exn ctx name') in
              Ctx.set ctx ~name ~value:curr;
              let prob_wo_cand = (eval_pmdf ctx exp) (Ctx.find_exn ctx name') in
              Ctx.set ctx ~name ~value:cand;
              acc +. prob_w_cand -. prob_wo_cand)
        in

        let alpha = Float.exp log_alpha in
        let uniform = Owl.Stats.std_uniform_rvs () in
        if Float.(uniform > alpha) then Ctx.set ctx ~name ~value:curr);

    if i >= a && i mod b = 0 then
      let (Ex ({ ty; _ } as query)) = query in
      let query =
        match ty with
        | Dist ty -> (
            match (ty, sample ctx query) with
            | Tyu, () -> 0.0
            | Tyi, i -> float_of_int i
            | Tyr, r -> r
            | Tyb, b -> if b then 1.0 else 0.0)
        | Data ty -> (
            match (ty, eval ctx query) with
            | Tyu, () -> 0.0
            | Tyi, i -> float_of_int i
            | Tyr, r -> r
            | Tyb, b -> if b then 1.0 else 0.0)
      in
      samples.((i - a) / b) <- query
  done;

  samples

let infer ?(filename : string = "out") ?(num_samples : int = 100_000)
    (graph : Graph.t) (query : some_det) : string =
  let samples = gibbs_sampling graph ~num_samples query in

  let filename = String.chop_suffix_if_exists filename ~suffix:".stp" in
  let plot_path = filename ^ ".png" in

  let open Owl_plplot in
  let h = Plot.create plot_path in
  Plot.set_title h (Printing.to_string query);
  let mat = Owl.Mat.of_array samples 1 num_samples in
  Plot.histogram ~h ~bin:50 mat;
  Plot.output h;
  plot_path
