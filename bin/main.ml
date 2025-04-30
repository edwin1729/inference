
(* Define the types *)
type exc = Exc of int

type e =
  | App of e * e
  | Abs of int * e
  | Var of int
  | Try of e * exc * e
  | Raise of exc * e
  | Val of int

type t =
  | LInt              (* Language Int *)
  | TyVar of int
  | TyAbs of int * t
  | EffAbs of int * t
  | Arr of t * sigma list * t (* arrow type *)
  | T (*Top, the type of a raise expression*)
and sigma =
  | Sig of t * t
  | EffVar of int

(* Create the Map from int to t *)
module IntMap = Map.Make(struct
  type t = int
  let compare = compare
end)

type context = Context of t IntMap.t (* Context where the int denotes a term variable *)
type subs = Subs of t IntMap.t  (* Substitution where int denotes a type variable *)

(* Define the infer function *)
let rec infer (context: context) (e : e) : subs * t = match e with
  | App (e, e2) ->      (Subs IntMap.empty, T)
  | Abs (int, e) ->    (Subs IntMap.empty, T)
  | Var int ->         (Subs IntMap.empty, T)
  | Try (e1, exc, e) -> (Subs IntMap.empty, T)
  | Raise (exc, e) ->  (Subs IntMap.empty, T)
  | Val int ->         (Subs IntMap.empty, T)

let substitute (subs: subs) (context: context): context = failwith ""

let unify (t1: t) (t2: t): subs = failwith ""
