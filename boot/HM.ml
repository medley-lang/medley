(* http://soft.vub.ac.be/~cfscholl/Capita-Selecta-2015/papers/2002%20Heeren.pdf
 *)
module Subst = Map.Make(Term.FreeVar)
module Gen = Map.Make(Term.FreeVar)
module Inst = Map.Make(Int)
type level = int

type constraints =
  | Eq of Term.ty * Term.ty
  | Sub of Term.ty * level * Term.ty
  | Inst of Term.ty * Term.ty_scheme

type mapping =
  | Solved of Term.ty
  | New_level of int

(** Apply a substitution to a type. *)
let rec apply subst = function
  | Term.Arrow(dom, codom) -> Term.Arrow(apply subst dom, apply subst codom)
  | Term.TyApp(tcon, targ) -> Term.TyApp(apply subst tcon, apply subst targ)
  | Term.Rigid r -> Term.Rigid r
  | Term.Unit -> Term.Unit
  | Term.Wobbly v ->
     match Subst.find_opt v subst with
     | Some ty -> ty
     | None -> Term.Wobbly v

(** Perform the occurs check. Also adjust the let-levels of the type variables
    to match the level of the type variable being solved for. *)
let rec occurs subst v ty =
  let open Util.Option in
  match ty with
  | Term.Arrow(dom, codom) ->
     let* subst = occurs subst v dom in
     occurs subst v codom
  | Term.TyApp(tcon, targ) ->
     let* subst = occurs subst v tcon in
     occurs subst v targ
  | Term.Rigid _ -> Some subst
  | Term.Wobbly w ->
     if w.Term.fv_id = v.Term.fv_id then
       None
     else if w.Term.level > v.Term.level then
       (* Adjust the level. *)
       Some
         (Subst.add w (Term.Wobbly { w with Term.level = v.Term.level }) subst)
     else
       Some subst
  | Term.Unit -> Some subst

(** Finds the most general unifier. Takes the substitution as an accumulator
    parameter. *)
let rec mgu subst lhs rhs =
  let open Util.Result in
  match lhs, rhs with
  | Term.Arrow(dom, codom), Term.Arrow(dom', codom') ->
     let* subst = mgu subst dom dom' in
     mgu subst (apply subst codom) (apply subst codom')
  | Term.TyApp(tcon, targ), Term.TyApp(tcon', targ') ->
     let* subst = mgu subst tcon tcon' in
     mgu subst (apply subst targ) (apply subst targ')
  | Term.Rigid r, Term.Rigid r' when r = r' -> Ok subst
  | Term.Wobbly v, Term.Wobbly v' when v.Term.fv_id = v'.Term.fv_id -> Ok subst
  | Term.Wobbly v, ty | ty, Term.Wobbly v ->
     begin match occurs subst v ty with
     | None -> Error (Error.Occurs(v, ty))
     | Some subst -> Ok (Subst.add v ty subst)
     end
  | Term.Unit, Term.Unit -> Ok subst
  | lhs, rhs -> Error (Error.Unification(lhs, rhs))

let rec inst insts = function
  | Term.Arrow(dom, codom) -> Term.Arrow(inst insts dom, inst insts codom)
  | Term.TyApp(tcon, targ) -> Term.TyApp(inst insts tcon, inst insts targ)
  | Term.Wobbly w -> Term.Wobbly w
  | Term.Unit -> Term.Unit
  | Term.Rigid r ->
     match Inst.find_opt r insts with
     | None -> Term.Rigid r
     | Some ty -> ty
