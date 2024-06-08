open! Core

type real = float
type _ ty = Tyu : unit ty | Tyi : int ty | Tyr : real ty | Tyb : bool ty
type _ data_ty = Data
type _ dist_ty = Dist
type _ cty = Data : 'a ty -> 'a data_ty cty | Dist : 'a ty -> 'a dist_ty cty

let string_of_ty : type a. a ty -> string = function
  | Tyu -> "unit"
  | Tyi -> "int"
  | Tyr -> "real"
  | Tyb -> "bool"

let string_of_cty : type a. a cty -> string = function
  | Data ty -> string_of_ty ty ^ " data"
  | Dist ty -> string_of_ty ty ^ " dist"

type _ params =
  | [] : unit params
  | ( :: ) : 'a ty * 'b params -> ('a * 'b) params

type det = Det
type non_det = Non_det

type _ vargs =
  | [] : unit vargs
  | ( :: ) : ('a ty * 'a) * 'b vargs -> ('a * 'b) vargs

type ('a, 'b) dist = {
  ret : 'a ty;
  name : Id.t;
  params : 'b params;
  sampler : 'b vargs -> 'a;
  log_pmdf : 'b vargs -> 'a -> real;
}

type ('a, 'b, 'c) bop = { name : Id.t; f : 'a -> 'b -> 'c }
type ('a, 'b) uop = { name : Id.t; f : 'a -> 'b }

type (_, _) args =
  | [] : (unit, _) args
  | ( :: ) : ('a data_ty, 'd) texp * ('b, 'd) args -> ('a * 'b, 'd) args

and (_, _) exp =
  | Value : 'a -> ('a data_ty, _) exp
  | Var : Id.t -> (_, non_det) exp
  | RVar : Id.t -> (_ data_ty, det) exp
  | Bop :
      ('a, 'b, 'c) bop * ('a data_ty, 'd) texp * ('b data_ty, 'd) texp
      -> ('c data_ty, 'd) exp
  | Uop : ('a, 'b) uop * ('a data_ty, 'd) texp -> ('b data_ty, 'd) exp
  (* TODO: Add list and record constructors *)
  (*| List : ('a, 'd) exp list -> ('a list, 'd) exp*)
  (*| Record : ('k * 'v, 'd) exp list -> ('k * 'v, 'd) exp*)
  | If : (bool data_ty, 'd) texp * ('a, 'd) texp * ('a, 'd) texp -> ('a, 'd) exp
  | Let : Id.t * ('a, non_det) texp * ('b, non_det) texp -> ('b, non_det) exp
  | Call : ('a, 'b) dist * ('b, 'd) args -> ('a dist_ty, 'd) exp
  | Sample : ('a dist_ty, non_det) texp -> ('a data_ty, non_det) exp
  | Observe :
      ('a dist_ty, non_det) texp * ('a data_ty, non_det) texp
      -> (unit data_ty, non_det) exp

and ('a, 'd) texp = { ty : 'a cty; exp : ('a, 'd) exp }

let rec fv : type a. (a, det) exp -> Id.Set.t = function
  | Value _ -> Id.Set.empty
  | RVar x -> Id.Set.singleton x
  | Bop (_, { exp = e1; _ }, { exp = e2; _ }) -> Id.(fv e1 @| fv e2)
  | Uop (_, { exp; _ }) -> fv exp
  | If ({ exp = e_pred; _ }, { exp = e_cons; _ }, { exp = e_alt; _ }) ->
      Id.(fv e_pred @| fv e_cons @| fv e_alt)
  | Call (_, args) -> fv_args args

and fv_args : type a. (a, det) args -> Id.Set.t = function
  | [] -> Id.Set.empty
  | { exp; _ } :: es -> Id.(fv exp @| fv_args es)

type some_ndet = Ex : (_, non_det) texp -> some_ndet
type some_det = Ex : (_, det) texp -> some_det
type some_pmdf = Ex : (_ dist_ty, det) texp -> some_pmdf
type some_cty = Ex : _ cty -> some_cty
type some_params = Ex : _ params -> some_params
type some_v = Ex : ('a ty * 'a) -> some_v
type some_dist = Ex : _ dist -> some_dist
