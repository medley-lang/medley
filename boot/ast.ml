type 'a node = {
    node : 'a;
  }

type ty =
  | Arrow of ty node * ty node
  | TyApp of ty node * ty node
  | TyVar of string
  | Unit

type ty_scheme = Forall of string list * ty node

type pat =
  | ConPat of string * pat node list
  | VarPat of string
  | WildPat

type expr =
  | App of expr node * expr node
  | Case of expr node list * clause list
  | Lam of clause list
  | Trivial
  | Var of string

and clause = {
    lhs : pat node list;
    rhs : expr node;
  }

type datacon_decl = {
    datacon_name : string;
    datacon_types : ty node list;
  }

type decl =
  | Data_decl of string * string list * datacon_decl list
  | Term_decl of string * ty_scheme option * expr node

type program = {
    decls : decl list;
  }
