type t =
  | Occurs of Term.FreeVar.t * Term.ty
  | Unification of Term.ty * Term.ty
  | Done
  | IntroTac
  | TrivialTac
  | UnknownTac
