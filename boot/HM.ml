(* http://soft.vub.ac.be/~cfscholl/Capita-Selecta-2015/papers/2002%20Heeren.pdf
 *)
(* http://gallium.inria.fr/~fpottier/publis/emlti-final.pdf *)
module Subst = Map.Make(Term.FreeVar)
module Gen = Map.Make(Term.FreeVar)
module Inst = Map.Make(Int)
type level = int

(** The Essence of ML Type Inference, Section 10.2 Constraints, Figure 10-4. *)
type constraints =
  | True
  | Conj of constraints * constraints
  | Exists of Term.wobbly * constraints
  | Let_in of (string, ty_scheme) Hashtbl.t * constraints
  | Sub of Term.ty * Term.ty
  | Inst of string * Term.ty

and ty_scheme = Forall of int list * constraints * Term.ty

(** Apply a substitution to a type. *)
let rec apply subst = function
  | Term.Arrow(dom, codom) -> Term.Arrow(apply subst dom, apply subst codom)
  | Term.TyApp(tcon, targ) -> Term.TyApp(apply subst tcon, apply subst targ)
  | Term.Bound_var bv -> Term.Bound_var bv
  | Term.Unit -> Term.Unit
  | Term.Free_var fv ->
     match Subst.find_opt fv subst with
     | Some ty -> ty
     | None -> Term.Free_var fv

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
  | Term.Bound_var _ -> Some subst
  | Term.Free_var w ->
     if w.Term.fv_id = v.Term.fv_id then
       None
     else if w.Term.level > v.Term.level then
       (* Adjust the level. *)
       Some
         (Subst.add w
            (Term.Free_var { w with Term.level = v.Term.level }) subst)
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
  | Term.Bound_var r, Term.Bound_var r' when r = r' -> Ok subst
  | Term.Free_var v, Term.Free_var v' when v.Term.fv_id = v'.Term.fv_id ->
     Ok subst
  | Term.Free_var v, ty | ty, Term.Free_var v ->
     begin match occurs subst v ty with
     | None -> Error (Error.Occurs(v, ty))
     | Some subst -> Ok (Subst.add v ty subst)
     end
  | Term.Unit, Term.Unit -> Ok subst
  | lhs, rhs -> Error (Error.Unification(lhs, rhs))

let rec inst insts = function
  | Term.Arrow(dom, codom) -> Term.Arrow(inst insts dom, inst insts codom)
  | Term.TyApp(tcon, targ) -> Term.TyApp(inst insts tcon, inst insts targ)
  | Term.Free_var w -> Term.Free_var w
  | Term.Unit -> Term.Unit
  | Term.Bound_var r ->
     match Inst.find_opt r insts with
     | None -> Term.Bound_var r
     | Some ty -> ty
