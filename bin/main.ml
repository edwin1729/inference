open Option
let ( % ) = Fun.compose

let (let*) v f = match v with
  | None -> None
  | Some x -> f x

(* Define the types *)
type exc = Exc of int

type e =
  | App of e * e
  | Abs of int * e
  | Var of int
  | Try of e * exc * e * e
  | Raise of exc * e
  | Val of int

type lType = (*language type*)
  | LInt              (* Language Int *)
  | TyVar of int
  | TyAbs of int * lType
  | EffAbs of int * lType
  | Arr of lType * row * lType (* arrow type *)
  | T (*Top, the type of a raise expression*)
and sigma =
  | Sig of exc
  | EffVar of int (*aka row variable*)
and row = sigma list ref (*This is mutable to make the unify function look cleaner*)

(* Used as map from int to lType *)
module IntMap = Map.Make(struct
  type t = int
  let compare = Int.compare
end)

(* Used as set of effect names*)
module IntSet = Set.Make(struct
  type t = int
  let compare = Int.compare
end)

open IntMap
(*type context = lType IntMap.t Context where the int denotes a term variable *)

type context = {ty: lType IntMap.t; eff: IntSet.t} (* Context where the int denotes a term variable *)
type subs = Subs of lType IntMap.t  (* Substitution where int denotes a type and row variables *)

let lookup ctx var =
  IntMap.find_opt var ctx

let freshT: unit -> int = (*fresh type variables*)
  let counter: int ref = ref 1 in
  fun () ->
    let v = !counter in
    incr counter;
    v

(*let freshE: unit -> int = (*fresh (effect) row variables*)
  let counter = ref -1 in
  fun () ->
    let v = !counter in
    decr counter;
    v*)

(*let subsContext (subs: subs) (context: context): context = failwith ""*)
let subsContext (subs: lType -> lType) (context: context): context = failwith ""
let subsLType (subs: subs) (t: lType): lType = failwith ""
let globalEffects (exc: exc): lType = failwith "" (*assuming no type variables here*)

(*Performs the subsumption rule as an when required. It feels natural for unify to universaldeal with subsumption
  But this is just a design choice. Another choice I've made is that if subsumption the new type needs to be
  returned. I've decided to try doing this by making row variables mutable references always*)
let unify (t1: lType) (t2: lType): (lType -> lType) option = failwith ""

(* Applies the typing rules enhanced by an implicit subsumption rule which is
   always applied through a call to unify *)
let rec infer (ctx: context) (e : e) : ((lType -> lType) * lType * row) option = match e with
  | App (e2, e1) ->
      let* (s1, t1, r1) = infer ctx e1 in
      let c1 = subsContext s1 ctx in
      let* (s2, t2, _r2) = infer c1 e2 in (* r2 should be [], Q. why is it not so in the typing rules *)
      let c2 = subsContext s2 c1 in
      let phi = TyVar (freshT ()) in
      (* insisting that t2 has the same row annotation as e1 (r1). Of course this means nothing
         since the call to unify uses subsumption. In other words the constraint we assert is always true
         insofar as row variables are concerned *)
      let* s3 = unify t2 (Arr (s2 t1, r1, phi)) in
      Some (s3 % s2 % s1, s3 phi, ref !r1) (*Following this clone pattern for now to ensure that unify never
                                             modifies rows higher up in the derivation tree. This is done
                                             conservatively/ naively for if these rows show up in the context*)
  | Abs (n2, e1) ->
      let t2 = TyVar (freshT ()) in
      let* (s1, t1, r1) = infer ({ctx with ty = add n2 t2 ctx.ty}) e1 in
      Some (s1, s1 (Arr (t2, ref !r1, t1)), ref [])
  | Var tyvar ->
      let* t = find_opt tyvar ctx.ty in
      Some (Fun.id, t, ref [])
  | Try (e1, (Exc n as exc), f_h, f_r) ->
      let* (s1, t1, r1) = infer ({ctx with eff = IntSet.add n ctx.eff}) e1 in
      let effTy = globalEffects exc in
      let c1 = subsContext s1 ctx in
      let* (s_h, t_h, r_h) =  infer c1 f_h in (* Shallow handler, should it be deep? *)
      let r1' = ref (List.filter (fun x -> x <> (Sig exc)) !r1) in
      let phi = TyVar (freshT ()) in
      let* s_h' = unify t_h (Arr (effTy, r1', phi)) in
      let c_h = subsContext (s_h' % s_h) c1 in
      let* (s_r, t_r, r_r) = infer c_h f_r in
      (*let* s_r' = unify t_r Arr (t1, r1', )*)
      failwith ""
  | Raise (exc, e) ->   failwith ""
  | Val _ ->          Some (Fun.id, LInt, ref [])
let () =
  let () = print_int (freshT ()) in
  print_int (freshT ())
