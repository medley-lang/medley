module ResultMonad = struct
  let (let+) r f = Result.map f r
  let (and+) l r = match l, r with
    | Ok l, Ok r -> Ok(l, r)
    | Ok _, Error e -> Error e
    | Error e, _ -> Error e
end

let rec from_ast_ty ty =
  let open ResultMonad in
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

type constraints =
  | Subtype of Term.ty * Term.ty

type state = {
    focus : Term.preterm;
    wobblyvar_supply : int;
    hole_supply : int;
    hole_map : Term.preterm Term.HoleMap.t;
    constraints : constraints list;
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
  ; wobblyvar_supply = 0
  ; hole_supply = 1
  ; hole_map = Term.HoleMap.empty
  ; constraints = [] }

let throw e state = (Error e, state)

let catch action handler state =
  let (result, state) = action state in
  match result with
  | Ok a -> (Ok a, state)
  | Error e -> handler e state

let get_state state = (Ok state, state)

let fresh_wobbly state =
  let x = state.wobblyvar_supply in
  (Ok x, { state with wobblyvar_supply = x + 1 })

let fresh_hole f state =
  let x = state.hole_supply in
  let preterm = f x in
  ( Ok preterm
  , { state with
      hole_map = Term.HoleMap.add x preterm state.hole_map
    ; hole_supply = x + 1 })

let get_focus state =
  (Ok state.focus, state)

let get_holes state =
  (Ok state.hole_map, state)

let modify f state =
  (Ok (), f state)

let subtype sub super =
  modify (fun state ->
      { state with
        constraints = Subtype(sub, super) :: state.constraints })

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
       let+ () = subtype (Term.Arrow(domain, codomain)) (Term.Wobbly wobbly) in
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
     let+ () = subtype Term.Unit (Term.Wobbly wobbly) in
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
