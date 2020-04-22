type level = int
type rigid = int
type wobbly = {
    fv_id : int;
    level : level;
  }

module FreeVar = struct
  type t = wobbly
  let compare lhs rhs = compare lhs.fv_id rhs.fv_id
end

type ty =
  | Arrow of ty * ty
  | TyApp of ty * ty
  | Rigid of rigid
  | Wobbly of wobbly
  | Unit

type ty_scheme = Forall of int list * ty

type pat =
  | ConPat
  | VarPat of string

module HoleMap = Map.Make(Int)

type preterm = {
    mutable parent : parent;
    mutable preterm : hole;
    tctx : (string, ty_scheme) Context.t;
    mutable expected_ty : ty;
  }

and parent =
  | Parent of preterm
  | Root

and hole =
  | Preterm of preterm'
  | Hole of int

and preterm' =
  | PreApp of wobbly * preterm * preterm
  (** The wobbly is the input type variable, as function application introduces
      this as an unknown type. *)
  | PreCase of preterm list * preterm clause list
  | PreLam of preterm clause list
  | PreTrivial
  | PreVar of string

and term =
  | App of term * term
  | Case of term list * term clause list
  | Lam of term clause list
  | Trivial
  | Var of string

and 'term clause = {
    lhs : pat * pat list;
    rhs : 'term;
  }

let rec print_ty prec = function
  | Arrow(domain, codomain) ->
     let s = print_ty 1 domain ^ " -> " ^ print_ty 0 codomain in
     if prec > 0 then
       "(" ^ s ^ ")"
     else
       s
  | TyApp(head, arg) ->
     let s = print_ty 2 head ^ " " ^ print_ty 3 arg in
     if prec > 2 then
       "(" ^ s ^ ")"
     else
       s
  | Rigid r -> "r" ^ string_of_int r
  | Wobbly w -> "?" ^ string_of_int w.fv_id
  | Unit -> "unit"
