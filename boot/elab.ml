let rec from_ast_ty ty =
  let open Util.Result in
  match ty.Ast.node with
  | Ast.Arrow(dom, codom) ->
     let+ dom = from_ast_ty dom
     and+ codom = from_ast_ty codom in
     Term.Arrow(dom, codom)
  | Ast.TyApp(tcon, targ) ->
     let+ tcon = from_ast_ty tcon
     and+ targ = from_ast_ty targ in
     Term.TyApp(tcon, targ)
  | Ast.TyVar _ -> Error ()
  | Ast.Unit -> Ok Term.Unit

type state = {
    focus : Term.preterm;
    level : int;
    bv_supply : int;
    fv_supply : int;
    hole_supply : int;
    hole_map : Term.preterm Term.HoleMap.t;
  }

type 'a t = state -> ('a, Error.t) result * state

module type MONAD = sig
  type 'a t
  val return : 'a -> 'a t
  val (let+) : 'a t -> ('a -> 'b) -> 'b t
  val (and+) : 'a t -> 'b t -> ('a * 'b) t
  val (and*) : 'a t -> 'b t -> ('a * 'b) t
  val (let*) : 'a t -> ('a -> 'b t) -> 'b t
end

(** The elaboration monad. *)
module Monad : MONAD with type 'a t = 'a t = struct
  type nonrec 'a t = 'a t

  let return a state = (Ok a, state)

  let (let+) action f state =
    let (result, state) = action state in
    (Result.map f result, state)

  let (and+) left right state =
    let (lopt, state) = left state in
    let (ropt, state) = right state in
    match lopt, ropt with
    | Error e, _ -> (Error e, state)
    | Ok _, Error e -> (Error e, state)
    | Ok l, Ok r -> (Ok (l, r), state)

  let (and*) = (and+)

  let (let*) action f state =
    let (opt, state) = action state in
    match opt with
    | Error e -> (Error e, state)
    | Ok a -> f a state
end

open Monad

let empty_state focus =
  { focus
  ; level = 0
  ; bv_supply = 0
  ; fv_supply = 0
  ; hole_supply = 1
  ; hole_map = Term.HoleMap.empty }

let throw e state = (Error e, state)

let catch action handler state =
  let (result, state) = action state in
  match result with
  | Ok a -> (Ok a, state)
  | Error e -> handler e state

let get_state state = (Ok state, state)

let fresh_fv state =
  let x = state.fv_supply in
  ( Ok { Term.fv_id = x; level = state.level }
  , { state with fv_supply = x + 1 } )

let fresh_bv state =
  let x = state.bv_supply in
  (Ok x, { state with bv_supply = x + 1 })

(** Let-generalization. *)
let rec gen bound_vars = function
  | Term.Arrow(dom, codom) ->
     let* bound_vars, dom = gen bound_vars dom in
     let+ bound_vars, codom = gen bound_vars codom in
     bound_vars, Term.Arrow(dom, codom)
  | Term.TyApp(tcon, targ) ->
     let* bound_vars, tcon = gen bound_vars tcon in
     let+ bound_vars, targ = gen bound_vars targ in
     bound_vars, Term.TyApp(tcon, targ)
  | Term.Bound_var r -> return (bound_vars, Term.Bound_var r)
  | Term.Unit -> return (bound_vars, Term.Unit)
  | Term.Free_var w ->
     let* state = get_state in
     if w.Term.level >= state.level then
       match HM.Gen.find_opt w bound_vars with
       | None ->
          let+ bv = fresh_bv in
          (HM.Gen.add w bv bound_vars, Term.Bound_var bv)
       | Some r -> return (bound_vars, Term.Bound_var r)
     else
       return (bound_vars, Term.Free_var w)

(** Given a map from free variables to bound variables, returns the bound
    variables as a list. *)
let bound_vars bvs =
  HM.Gen.to_seq bvs
  |> Seq.map (fun (_, v) -> v)
  |> List.of_seq

(** Generalize the monotype. *)
let generalize ty =
  let+ bvs, ty = gen HM.Gen.empty ty in
  Term.Forall(bound_vars bvs, ty)

let exists f =
  let* fv = fresh_fv in
  let+ c = f fv in
  HM.Exists(fv, c)

let lam_pat_has_type bindings pat ty =
  match pat.Ast.node with
  | Ast.ConPat _ -> failwith "Unimplemented"
  | Ast.TrivialPat -> return (HM.Sub(Term.Unit, ty))
  | Ast.VarPat name ->
     begin match Hashtbl.find_opt bindings name with
     | None ->
        Hashtbl.add bindings name (HM.Forall([], HM.True, ty));
        return HM.True
     | Some _ -> throw (Error.Redefined_var name)
     end
  | Ast.WildPat -> return HM.True

let let_pat_has_ty bindings bvs pat ty : (int list * HM.constraints) t =
  match pat.Ast.node with
  | Ast.TrivialPat -> return (bvs, HM.Sub(Term.Unit, ty))
  | Ast.VarPat name ->
     begin match Hashtbl.find_opt bindings name with
     | None ->
        let+ bv = fresh_bv in
        Hashtbl.add bindings name bv;
        bv :: bvs, HM.Sub(ty, Term.Bound_var bv)
     | Some _ -> throw (Error.Redefined_var name)
     end
  | _ -> failwith "Unimplemented"

let rec let_pats_have_tys prebindings list pats
        : ((int list * HM.constraints) list) t =
  match list, pats with
  | [], [] -> return []
  | ((ty, _c) :: tys), (pat :: pats) ->
     let* pair = let_pat_has_ty prebindings [] pat ty in
     let+ list = let_pats_have_tys prebindings tys pats in
     pair :: list
  | [], _ :: _ -> throw Error.Done
  | _ :: _, [] -> throw Error.Done

(** The Essence of ML Type Inference, Section 10.4 Constraint Generation, Figure
    10-9. *)
let rec has_type expr ty =
  match expr.Ast.node with
  | Ast.Var name -> return (HM.Inst(name, ty))
  | Ast.App(t, u) ->
     exists (fun fv ->
         let* c1 = has_type t (Term.Arrow(Term.Free_var fv, ty)) in
         let+ c2 = has_type u (Term.Free_var fv) in
         HM.Conj(c1, c2))
  | Ast.Lam clauses ->
     List.fold_left (fun acc next ->
         let pat, pats = next.Ast.lhs in
         let bindings = Hashtbl.create 11 in
         let* c1 = acc in
         let+ c2 = lam_clause bindings ty (pat :: pats) next.Ast.rhs in
         HM.Conj(c1, c2)) (return HM.True) clauses
  | Ast.Case(scruts, clauses) ->
     let* list =
       List.fold_left (fun acc next ->
           let* list = acc in
           let* bv = fresh_bv in
           let+ c = has_type next (Term.Bound_var bv) in
           (Term.Bound_var bv, c) :: list) (return []) scruts
     in
     List.fold_left (fun acc next ->
         let* cs = acc in
         let pat, pats = next.Ast.lhs in
         (* Prebindings is a "helper" that maps names to type variables. *)
         let prebindings = Hashtbl.create 11 in
         let* list = let_pats_have_tys prebindings list (pat :: pats) in
         let bindings = Hashtbl.create 11 in
         (* Add all the variables encountered in the patterns to the context *)
         List.iter (fun (bvs, cs) ->
             Hashtbl.iter (fun name bv ->
                 Hashtbl.add bindings name
                   (HM.Forall(bvs, cs, Term.Bound_var bv))
               ) prebindings
           ) list;
         let+ c = has_type next.Ast.rhs ty in
         HM.Conj(HM.Let_in(bindings, c), cs)) (return HM.True) clauses
  | Ast.Trivial -> return (HM.Sub(Term.Unit, ty))

and lam_clause bindings expected_ty pats rhs =
  match pats with
  | [] ->
     let+ c = has_type rhs expected_ty in
     HM.Let_in(bindings, c)
  | pat :: pats ->
     exists (fun fv1 ->
         let x1 = Term.Free_var fv1 in
         exists (fun fv2 ->
             let x2 = Term.Free_var fv2 in
             let* c1 = lam_pat_has_type bindings pat x2 in
             let+ c2 = lam_clause bindings x1 pats rhs in
             HM.Conj(HM.Conj(c1, c2), HM.Sub(Term.Arrow(x1, x2), expected_ty))))

(*
(** Operations on holes. *)

let fresh_hole f state =
  let x = state.hole_supply in
  let preterm = f x in
  ( Ok preterm
  , { state with
      hole_map = Term.HoleMap.add x preterm state.hole_map
    ; hole_supply = x + 1 } )

let get_focus state =
  (Ok state.focus, state)

let get_holes state =
  (Ok state.hole_map, state)

let modify f state =
  (Ok (), f state)

let eq lhs rhs =
  modify (fun state ->
      { state with
        constraints = HM.Eq(lhs, rhs) :: state.constraints })

let inst monotype ty_scheme =
  modify (fun state ->
      { state with
        constraints = HM.Inst(monotype, ty_scheme) :: state.constraints })

let fill tactic focus =
  let+ preterm = tactic focus in
  let old = focus.Term.preterm in
  focus.preterm <- Preterm preterm;
  old

let solve tactic =
  let* focus = get_focus in
  let* old = fill tactic focus in
  let* () = match old with
    | Term.Hole hole_id ->
       modify (fun state ->
           { state with hole_map = Term.HoleMap.remove hole_id state.hole_map }
         )
    | _ -> return ()
  in
  let* holes = get_holes in
  match Term.HoleMap.choose_opt holes with
  | Some (_, preterm) ->
     modify (fun state ->
         { state with focus = preterm }
       )
  | None -> throw Error.Done

(** Tactics. *)

let intro var focus =
  let* (domain, codomain) =
    match focus.Term.expected_ty with
    | Term.Arrow(domain, codomain) -> return (domain, codomain)
    | Term.Wobbly wobbly ->
       let* t0 = fresh_wobbly
       and* t1 = fresh_wobbly in
       let domain = Term.Wobbly t0
       and codomain = Term.Wobbly t1 in
       let+ () = eq (Term.Arrow(domain, codomain)) (Term.Wobbly wobbly) in
       (domain, codomain)
    | _ -> throw Error.IntroTac
  in
  let+ rhs =
    fresh_hole
      (fun hole ->
        { parent = Parent focus
        ; preterm = Hole hole
        ; tctx =
            (let tctx = Context.extend focus.tctx in
             ignore (Context.add tctx var (Forall([], domain)));
             tctx)
        ; expected_ty = codomain })
  in
  let clause = Term.{ lhs = (VarPat var, []); rhs } in
  Term.PreLam [clause]

let trivial focus =
  match focus.Term.expected_ty with
  | Term.Unit -> return Term.PreTrivial
  | Term.Wobbly wobbly ->
     let+ () = eq Term.Unit (Term.Wobbly wobbly) in
     Term.PreTrivial
  | _ -> throw Error.TrivialTac

let apply focus =
  let goal = focus.Term.expected_ty
  and parent = Term.Parent focus in
  let* wobbly = fresh_wobbly in
  let+ fun_hole =
    fresh_hole
      (fun hole ->
        { Term.parent = parent
        ; preterm = Hole hole
        ; tctx = focus.tctx
        ; expected_ty = Arrow(Wobbly wobbly, goal) })
  and+ arg_hole =
    fresh_hole
      (fun hole ->
        { Term.parent = parent
        ; preterm = Hole hole
        ; tctx = focus.tctx
        ; expected_ty = Wobbly wobbly })
  in
  Term.PreApp(wobbly, fun_hole, arg_hole)
 *)
