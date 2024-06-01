open Core
open Program

module Env = struct
  type t = (Id.t, fn, Id.comparator_witness) Map.t

  let empty : t = Map.empty (module Id)
  let add (env : t) ~(name : Id.t) ~(fn : fn) = Map.add env ~key:name ~data:fn
  let find_exn (env : t) ~(name : Id.t) : fn = Map.find_exn env name
end

module Pred = struct
  type t = Empty | And of Det_exp.t * t | And_not of Det_exp.t * t

  let rec fv : t -> Set.M(Id).t = function
    | Empty -> Set.empty (module Id)
    | And (de, p) | And_not (de, p) -> Set.union (Det_exp.fv de) (fv p)
end

module Dist = struct
  type t
  type one = One

  type exp =
    | If_de of Det_exp.t * exp * exp
    | If_pred of Pred.t * exp * one
    | Dist_obj of { dist : t; var : Id.t; args : Det_exp.t list }

  exception Score_invalid_arguments

  let prim_to_dist : Id.t -> t = failwith "Not implemented"

  let rec score (det_exp : Det_exp.t) (var : Id.t) =
    match det_exp with
    | If (e_pred, e_con, e_alt) ->
        let s_con = score e_con var in
        let s_alt = score e_alt var in
        If_de (e_pred, s_con, s_alt)
    | Prim_call (c, es) -> Dist_obj { dist = prim_to_dist c; var; args = es }
    | _ -> raise Score_invalid_arguments
end

module Graph = struct
  type vertex = Id.t
  type arc = vertex * vertex
  type det_map = (Id.t, Dist.exp, Id.comparator_witness) Map.t
  type obs_map = (Id.t, Det_exp.t, Id.comparator_witness) Map.t

  type t = {
    vertices : vertex list;
    arcs : arc list;
    det_map : det_map;
    obs_map : obs_map;
  }

  let empty =
    {
      vertices = [];
      arcs = [];
      det_map = Map.empty (module Id);
      obs_map = Map.empty (module Id);
    }

  let union g1 g2 =
    {
      vertices = g1.vertices @ g2.vertices;
      arcs = g1.arcs @ g2.arcs;
      det_map =
        Map.merge g1.det_map g2.det_map ~f:(fun ~key:_ v ->
            match v with
            | `Left det | `Right det -> Some det
            | `Both _ ->
                failwith "Graph.union: duplicate deterministic expression");
      obs_map =
        Map.merge g1.obs_map g2.obs_map ~f:(fun ~key:_ v ->
            match v with
            | `Left obs | `Right obs -> Some obs
            | `Both _ -> failwith "Graph.union: duplicate observation");
    }
end

let ( @+ ) = Graph.union

let gen_sym =
  let cnt = ref 0 in
  fun () ->
    incr cnt;
    Printf.sprintf "#%d" !cnt

let gen_vertex =
  let cnt = ref 0 in
  fun () ->
    incr cnt;
    Printf.sprintf "X%d" !cnt

let rec sub (exp : Exp.t) (x : Id.t) (det_exp : Det_exp.t) : Exp.t =
  let sub' exp = sub exp x det_exp in
  match exp with
  | Int n -> Int n
  | Real r -> Real r
  | Var y when Id.(x = y) -> Det_exp.to_exp det_exp
  | Var y -> Var y
  | Add (e1, e2) -> Add (sub' e1, sub' e2)
  | Radd (e1, e2) -> Radd (sub' e1, sub' e2)
  | Minus (e1, e2) -> Minus (sub' e1, sub' e2)
  | Rminus (e1, e2) -> Rminus (sub' e1, sub' e2)
  | Neg e -> Neg (sub' e)
  | Rneg e -> Rneg (sub' e)
  | Mult (e1, e2) -> Mult (sub' e1, sub' e2)
  | Rmult (e1, e2) -> Rmult (sub' e1, sub' e2)
  | Div (e1, e2) -> Div (sub' e1, sub' e2)
  | Rdiv (e1, e2) -> Rdiv (sub' e1, sub' e2)
  | Eq (e1, e2) -> Eq (sub' e1, sub' e2)
  | Noteq (e1, e2) -> Noteq (sub' e1, sub' e2)
  | Less (e1, e2) -> Less (sub' e1, sub' e2)
  | And (e1, e2) -> And (sub' e1, sub' e2)
  | Or (e1, e2) -> Or (sub' e1, sub' e2)
  | Seq (e1, e2) -> Seq (sub' e1, sub' e2)
  | Not e -> Not (sub' e)
  | List es -> List (List.map es ~f:sub')
  | Record fs -> Record (List.map fs ~f:(fun (f, e) -> (f, sub' e)))
  | Assign (y, e, body) when Id.(x = y) -> Assign (y, sub' e, body)
  | Assign (y, e, body) when not (Set.mem (Det_exp.fv det_exp) y) ->
      Assign (y, sub' e, sub' body)
  | Assign (y, e, body) ->
      let z = gen_sym () in
      Assign (z, sub' e, sub' @@ sub body y (Det_exp.Var z))
  | If (e_pred, e_con, e_alt) -> If (sub' e_pred, sub' e_con, sub' e_alt)
  | Call (f, es) -> Call (f, List.map es ~f:sub')
  | Sample e -> Sample (sub' e)
  | Observe (e1, e2) -> Observe (sub' e1, sub' e2)

exception Not_closed_observation

let compile (env : Env.t) (pred : Pred.t) (exp : Exp.t) : Graph.t * Det_exp.t =
  let rec compile pred =
    let compile' = compile pred in
    function
    | Exp.Int n -> (Graph.empty, Det_exp.Int n)
    | Real r -> (Graph.empty, Det_exp.Real r)
    | Var x -> (Graph.empty, Det_exp.Var x)
    | Sample e ->
        let g, de = compile' e in
        let v = gen_vertex () in
        let de_fvs = Det_exp.fv de in
        let f = Dist.score de v in
        let g' =
          Graph.
            {
              vertices = [ v ];
              arcs = List.map (Set.to_list de_fvs) ~f:(fun z -> (z, v));
              det_map = Map.singleton (module Id) v f;
              obs_map = Map.empty (module Id);
            }
        in
        (g @+ g', Det_exp.Var v)
    | Observe (e1, e2) ->
        let g1, de1 = compile' e1 in
        let g2, de2 = compile' e2 in
        let v = gen_vertex () in
        let f1 = Dist.score de1 v in
        let f = Dist.(If_pred (pred, f1, One)) in
        let fvs = Set.union (Det_exp.fv de1) (Pred.fv pred) in
        if not @@ Set.is_empty (Det_exp.fv de2) then
          raise Not_closed_observation;
        let g' =
          Graph.
            {
              vertices = [ v ];
              arcs = List.map (Set.to_list fvs) ~f:(fun z -> (z, v));
              det_map = Map.singleton (module Id) v f;
              obs_map = Map.singleton (module Id) v de2;
            }
        in
        (g1 @+ g2 @+ g', de2)
    | Assign (x, e, body) ->
        let g1, det_exp1 = compile' e in
        let sub_body = sub body x det_exp1 in
        let g2, det_exp2 = compile' sub_body in
        let g = g1 @+ g2 in
        (g, det_exp2)
    | If (e_pred, e_con, e_alt) ->
        let g1, det_exp_pred = compile' e_pred in
        let pred_true = Pred.And (det_exp_pred, pred) in
        let pred_false = Pred.And_not (det_exp_pred, pred) in
        let g2, det_exp_con = compile pred_true e_con in
        let g3, det_exp_alt = compile pred_false e_alt in
        let g = g1 @+ g2 @+ g3 in
        (g, Det_exp.If (det_exp_pred, det_exp_con, det_exp_alt))
    | Call (c, params) ->
        let f = Env.find_exn env ~name:c in
        let g, det_exps =
          List.fold_map params ~init:Graph.empty ~f:(fun g e ->
              let g', de = compile' e in
              (g @+ g', de))
        in
        let { params; body; _ } = f in
        let param_det_pairs = List.zip_exn params det_exps in
        let sub_body =
          List.fold param_det_pairs ~init:body
            ~f:(fun acc (param_name, det_exp) -> sub acc param_name det_exp)
        in
        let g_body, det_exp_body = compile' sub_body in
        (g @+ g_body, det_exp_body)
    | Add (e1, e2) ->
        let g1, de1 = compile' e1 in
        let g2, de2 = compile' e2 in
        (g1 @+ g2, Det_exp.Add (de1, de2))
    | Radd (e1, e2) ->
        let g1, de1 = compile' e1 in
        let g2, de2 = compile' e2 in
        (g1 @+ g2, Det_exp.Radd (de1, de2))
    | Minus (e1, e2) ->
        let g1, de1 = compile' e1 in
        let g2, de2 = compile' e2 in
        (g1 @+ g2, Det_exp.Minus (de1, de2))
    | Rminus (e1, e2) ->
        let g1, de1 = compile' e1 in
        let g2, de2 = compile' e2 in
        (g1 @+ g2, Det_exp.Rminus (de1, de2))
    | Neg e ->
        let g, de = compile' e in
        (g, Det_exp.Neg de)
    | Rneg e ->
        let g, de = compile' e in
        (g, Det_exp.Rneg de)
    | Mult (e1, e2) ->
        let g1, de1 = compile' e1 in
        let g2, de2 = compile' e2 in
        (g1 @+ g2, Det_exp.Mult (de1, de2))
    | Rmult (e1, e2) ->
        let g1, de1 = compile' e1 in
        let g2, de2 = compile' e2 in
        (g1 @+ g2, Det_exp.Rmult (de1, de2))
    | Div (e1, e2) ->
        let g1, de1 = compile' e1 in
        let g2, de2 = compile' e2 in
        (g1 @+ g2, Det_exp.Div (de1, de2))
    | Rdiv (e1, e2) ->
        let g1, de1 = compile' e1 in
        let g2, de2 = compile' e2 in
        (g1 @+ g2, Det_exp.Rdiv (de1, de2))
    | Eq (e1, e2) ->
        let g1, de1 = compile' e1 in
        let g2, de2 = compile' e2 in
        (g1 @+ g2, Det_exp.Eq (de1, de2))
    | Noteq (e1, e2) ->
        let g1, de1 = compile' e1 in
        let g2, de2 = compile' e2 in
        (g1 @+ g2, Det_exp.Noteq (de1, de2))
    | Less (e1, e2) ->
        let g1, de1 = compile' e1 in
        let g2, de2 = compile' e2 in
        (g1 @+ g2, Det_exp.Less (de1, de2))
    | And (e1, e2) ->
        let g1, de1 = compile' e1 in
        let g2, de2 = compile' e2 in
        (g1 @+ g2, Det_exp.And (de1, de2))
    | Or (e1, e2) ->
        let g1, de1 = compile' e1 in
        let g2, de2 = compile' e2 in
        (g1 @+ g2, Det_exp.Or (de1, de2))
    | Seq (e1, e2) ->
        let g1, _ = compile' e1 in
        let g2, de2 = compile' e2 in
        (g1 @+ g2, de2)
    | Not e ->
        let g, de = compile' e in
        (g, Det_exp.Not de)
    | Exp.List es ->
        let g, des =
          List.fold_map es ~init:Graph.empty ~f:(fun g e ->
              let g', de = compile' e in
              (g @+ g', de))
        in
        (g, Det_exp.List des)
    | Record fields ->
        let g, des =
          List.fold_map fields ~init:Graph.empty ~f:(fun g (k, v) ->
              let g_k, de_k = compile' k in
              let g_v, de_v = compile' v in
              (g @+ g_k @+ g_v, (de_k, de_v)))
        in
        (g, Det_exp.Record des)
  in
  compile pred exp
