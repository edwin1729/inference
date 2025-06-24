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
  | T (*Top, the type of a raise expression*)
  | LInt              (* Language Int *)
  | TyVar of int
  | Arr of lType * row * lType (* arrow type *)
(*  | TyAbs of int * lType*)
(*  | EffAbs of int * lType*)
and sigma =
  | Sig of exc
  | EffVar of int (*aka row variable*)
and row = sigma list ref (*This is mutable to make the unify function look cleaner*)

let compareSig (s1: sigma) (s2: sigma): int = match (s1, s2) with
    (Sig (Exc n1), Sig (Exc n2)) -> Int.compare n1 n2
  | ((Sig exc), (EffVar n)) -> -1
  | ((EffVar n), (Sig exc)) -> 1
  | ((EffVar n1), (EffVar n2)) -> Int.compare n1 n2

(* Used as set of effect names*)
module RowSet = Set.Make(struct
  type t = sigma
  let compare = compareSig
end)

let rec mapLType (f: int -> lType) (t: lType): lType = match t with
   LInt -> LInt
  | (TyVar (n)) -> f n
  | (Arr (t1, r, t2)) -> Arr (mapLType f t1, r, mapLType f t2) (*rows don't have type variables*)
  | T -> T

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

type context = {ty: lType IntMap.t; eff: IntSet.t} (* Context where for `ty` the int denotes a term variable *)
(*outdated*)type subs = Subs of lType IntMap.t  (* Substitution where int denotes a type and row variables *)

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
let subsContext (subs: lType -> lType) (ctx: context): context = IntMap.map subs ctx.ty
let globalEffects ((Exc n): exc): lType = match n with (*assuming no type variables here*)
  1 -> LInt
  | 2 -> Arr (LInt, ref [], LInt)

let rowSubsume (r1: row) (r2: row) =
  let rs1 = List.fold_left (fun acc x -> RowSet.add x acc) RowSet.empty !r1 in
  let rs2 = List.fold_left (fun acc x -> RowSet.add x acc) RowSet.empty !r2 in
  let union = RowSet.elements (RowSet.union rs1 rs2) in
  r1 := union;
  r2 := union

(*Performs the subsumption rule as an when required. It feels natural for unify to universaldeal with subsumption
  But this is just a design choice. Another choice I've made is that if subsumption the new type needs to be
  returned. I've decided to try doing this by making row variables mutable references always*)
let rec unify (t1: lType) (t2: lType): (lType -> lType) option = match (t1, t2) with
  (_, T) -> Some (Fun.id)
  |(T, _) -> Some (Fun.id)
  |(LInt, LInt) -> Some (Fun.id)
  |(LInt, _) -> None (* where does the opposite case go? *)
  |(TyVar n, ty) -> Some (mapLType (fun n -> ty))
  |(Arr (t1, r, t2), LInt) -> None
  |(Arr (t1, r, t2) as arr, (TyVar n as tyvar)) -> unify tyvar arr
  |(Arr (t1, r, t2), Arr (t1', r', t2')) ->
    let* s1 = unify t1 t1' in
    let* s2 = unify (s1 t2) (s1 t2') in
    let _ = rowSubsume r r' in
    Some (s2 % s1)

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
  | Try (e1, (Exc n as exc), h, r) ->
      let* (s1, t1, r1) = infer ({ctx with eff = IntSet.add n ctx.eff}) e1 in
      let effTy = globalEffects exc in
      let c1 = subsContext s1 ctx in
      let* (s_h, t_h, r_h) =  infer c1 h in
      let r1' = ref (List.filter (fun x -> x <> (Sig exc)) !r1) in
      let phi = TyVar (freshT ()) in
      let* s_h' = unify t_h (Arr (effTy, r1', phi)) in (*fresh ref?*)
      let c_h = subsContext (s_h' % s_h) c1 in
      let* (s_r, t_r, r_r) = infer c_h r in
      let* s_r' = unify t_r (Arr (t1, r1', s_r phi)) in (*fresh ref?*)
      Some (s_r' % s_r % s_h' % s_h, (s_r' % s_r) phi, r1')
  | Raise (Exc n as exc, e) ->
      let* _ = IntSet.find_opt n ctx.eff in
      let* (s, t, r) = infer ctx e in
      let effTy = globalEffects exc in (*no type var allowed*)
      let _s = unify t effTy in (*must be id subs, so ignore*)
      Some (s, T, ref [])
  | Val _ -> Some (Fun.id, LInt, ref [])
let () =
  let () = print_int (freshT ()) in
  print_int (freshT ())
