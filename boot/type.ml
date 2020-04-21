type kind =
  | KStar
  | KArrow of kind * kind

type ty =
  | Arrow of ty * ty
  | TyApp of ty * ty
  | TyVar of tvar ref
  | Unit

and tvar =
  | Rigid
  | Solved of ty
  | Wobbly
