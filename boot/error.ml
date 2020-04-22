type t =
  | Occurs of Term.FreeVar.t * Term.ty
  | Unification of Term.ty * Term.ty
  | Redefined_var of string
  | Done
  | IntroTac
  | TrivialTac
  | UnknownTac
