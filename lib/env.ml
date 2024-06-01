open Core
open Program

type t = fn Map.M(Id).t

let empty : t = Map.empty (module Id)
let add (env : t) ~(name : Id.t) ~(fn : fn) = Map.add env ~key:name ~data:fn
let find_exn (env : t) ~(name : Id.t) : fn = Map.find_exn env name
