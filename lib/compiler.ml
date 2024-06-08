open! Core
open Parse_tree
open Typed_tree

type env = some_det Id.Map.t

let gen_vertex =
  let cnt = ref 0 in
  fun () ->
    let v = "X" ^ string_of_int !cnt in
    incr cnt;
    v

exception Not_closed_observation

let rec peval : type a. (a data_ty, det) texp -> (a data_ty, det) texp =
 fun { ty; exp } ->
  match exp with
  | (Value _ | RVar _) as e -> { ty; exp = e }
  | Bop (op, te1, te2) -> (
      match (peval te1, peval te2) with
      | { exp = Value v1; _ }, { exp = Value v2; _ } ->
          { ty; exp = Value (op.f v1 v2) }
      | te1, te2 -> { ty; exp = Bop (op, te1, te2) })
  | Uop (op, te) -> (
      match peval te with
      | { exp = Value v; _ } -> { ty; exp = Value (op.f v) }
      | e -> { ty; exp = Uop (op, e) })
  | If (te_pred, te_cons, te_alt) -> (
      match peval te_pred with
      | { exp = Value true; _ } -> peval te_cons
      | { exp = Value false; _ } -> peval te_alt
      | te_pred -> { ty; exp = If (te_pred, peval te_cons, peval te_alt) })

let rec peval_args : type a. (a, det) args -> (a, det) args * a vargs option =
  function
  | [] -> ([], Some [])
  | te :: tl -> (
      match (peval te, peval_args tl) with
      | { ty = Data ty; exp = Value v }, (tl, Some vargs) ->
          ({ ty = Data ty; exp = Value v } :: tl, Some ((ty, v) :: vargs))
      | te, (tl, _) -> (te :: tl, None))

let rec score : type a. (a dist_ty, det) texp -> (a dist_ty, det) texp =
  function
  | { ty; exp = If (te_pred, te_con, te_alt) } -> (
      match peval te_pred with
      | { exp = Value true; _ } -> score te_con
      | { exp = Value false; _ } -> score te_alt
      | te_pred -> { ty; exp = If (te_pred, score te_con, score te_alt) })
  | { ty; exp = Call (f, args) } -> (
      let args : _ args = args in
      match peval_args args with
      | args, None -> { ty; exp = Call (f, args) }
      | _, Some vargs ->
          (* All arguments are fully evaluated;
             Go ahead and fully evaluate the (primitive) call.
             It is a primitive call as this is a deterministic expression. *)
          {
            ty;
            exp =
              Call
                ( {
                    ret = f.ret;
                    name = f.name;
                    params = [];
                    sampler = (fun [] -> f.sampler vargs);
                    log_pmdf = (fun [] -> f.log_pmdf vargs);
                  },
                  [] );
          })

type pred = (bool data_ty, det) texp

let rec compile :
    type a. env:env -> pred:pred -> (a, non_det) texp -> Graph.t * (a, det) texp
    =
 fun ~env ~pred { ty; exp } ->
  match exp with
  | Value v -> (Graph.empty, { ty; exp = Value v })
  | Var x -> (
      let (Ex { ty = tyx; exp }) = Map.find_exn env x in
      match (tyx, ty) with
      | Data Tyu, Data Tyu -> (Graph.empty, { ty; exp })
      | Data Tyi, Data Tyi -> (Graph.empty, { ty; exp })
      | Data Tyr, Data Tyr -> (Graph.empty, { ty; exp })
      | Data Tyb, Data Tyb -> (Graph.empty, { ty; exp })
      | Dist Tyu, Dist Tyu -> (Graph.empty, { ty; exp })
      | Dist Tyi, Dist Tyi -> (Graph.empty, { ty; exp })
      | Dist Tyr, Dist Tyr -> (Graph.empty, { ty; exp })
      | Dist Tyb, Dist Tyb -> (Graph.empty, { ty; exp })
      | _, _ -> assert false)
  | Bop (op, e1, e2) ->
      let g1, te1 = compile ~env ~pred e1 in
      let g2, te2 = compile ~env ~pred e2 in
      Graph.(g1 @| g2, { ty; exp = Bop (op, te1, te2) })
  | Uop (op, e) ->
      let g, te = compile ~env ~pred e in
      (g, { ty; exp = Uop (op, te) })
  | If (e_pred, e_con, e_alt) -> (
      let g1, de_pred = compile ~env ~pred e_pred in
      let pred_con =
        peval
          {
            ty = Data Tyb;
            exp = Bop ({ f = ( && ); name = "&&" }, pred, de_pred);
          }
      in
      let pred_alt =
        peval
          {
            ty = Data Tyb;
            exp =
              Bop
                ( { f = ( && ); name = "&&" },
                  pred,
                  {
                    ty = Data Tyb;
                    exp = Uop ({ f = not; name = "!" }, de_pred);
                  } );
          }
      in
      let g2, de_con = compile ~env ~pred:pred_con e_con in
      let g3, de_alt = compile ~env ~pred:pred_alt e_alt in
      let g = Graph.(g1 @| g2 @| g3) in
      match pred_con.exp with
      | Value true -> (g, de_con)
      | Value false -> (g, de_alt)
      | _ -> (g, { ty; exp = If (de_pred, de_con, de_alt) }))
  | Let (x, e, body) ->
      let g1, det_exp1 = compile ~env ~pred e in
      let g2, det_exp2 =
        compile ~env:(Map.set env ~key:x ~data:(Ex det_exp1)) ~pred body
      in
      Graph.(g1 @| g2, det_exp2)
  | Call (f, args) ->
      let g, args = compile_args env pred args in
      (g, { ty; exp = Call (f, args) })
  | Sample e ->
      let g, de = compile ~env ~pred e in
      let v = gen_vertex () in
      let de_fvs = fv de.exp in
      let f : some_pmdf = Ex (score de) in
      let g' =
        Graph.
          {
            vertices = [ v ];
            arcs = List.map (Set.to_list de_fvs) ~f:(fun z -> (z, v));
            pmdf_map = Id.Map.singleton v f;
            obs_map = Id.Map.empty;
          }
      in
      Graph.(g @| g', { ty; exp = RVar v })
  | Observe (e1, e2) ->
      let g1, de1 = compile ~env ~pred e1 in
      let g2, de2 = compile ~env ~pred e2 in
      let v = gen_vertex () in
      let f1 = score de1 in
      let (Dist ty) = f1.ty in
      let f =
        {
          ty = Dist ty;
          exp = If (pred, f1, { ty = Dist ty; exp = Call (Dist.one ty, []) });
        }
      in
      let fvs = Id.(fv de1.exp @| fv pred.exp) in
      let observed : some_v =
        match peval de2 with
        | { ty = Data ty; exp = Value v } -> Ex (ty, v)
        | _ -> raise Not_closed_observation
      in
      let g' =
        Graph.
          {
            vertices = [ v ];
            arcs = List.map (Set.to_list fvs) ~f:(fun z -> (z, v));
            pmdf_map = Id.Map.singleton v (Ex f : some_pmdf);
            obs_map = Id.Map.singleton v observed;
          }
      in
      Graph.(g1 @| g2 @| g', { ty = Data Tyu; exp = Value () })

and compile_args :
    type a. env -> pred -> (a, non_det) args -> Graph.t * (a, det) args =
 fun env pred args ->
  match args with
  | [] -> (Graph.empty, [])
  | arg :: args ->
      let g, arg = compile ~env ~pred arg in
      let g', args = compile_args env pred args in
      Graph.(g @| g', arg :: args)

let compile_program (prog : program) : Graph.t * some_det =
  let (Ex e) = Typing.check_program prog in
  let g, e =
    compile ~env:Id.Map.empty ~pred:{ ty = Data Tyb; exp = Value true } e
  in
  (g, Ex e)
