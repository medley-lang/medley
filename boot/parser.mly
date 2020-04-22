%token FORALL
%token FUN
%token DATA
%token DEF
%token UNIT
%token BAR
%token LPAREN
%token RPAREN
%token ARROW
%token COLON
%token COMMA
%token EQUALS
%token UNDERSCORE
%token <string> UIDENT
%token <string> LIDENT

%token EOF

%start <Ast.program> program
%start <Ast.ty_scheme> toplevel_ty_scheme

%%

let program :=
  | decls = list(decl); EOF; { Ast.{ decls } }

let toplevel_ty_scheme :=
  | ~ = ty_scheme; EOF; { ty_scheme }

let decl :=
  | DATA; name = UIDENT; params = list(LIDENT);
    EQUALS; option(BAR); datacons = list(BAR; datacon);
    { Ast.Data_decl(name, params, datacons) }
  | DEF; name = LIDENT; ty = option(COLON; ty_scheme); EQUALS; ~ = expr;
    { Ast.Term_decl(name, ty, expr) }

let datacon :=
  | name = UIDENT; types = list(ty3);
    { Ast.{ datacon_name = name; datacon_types = types } }

let ty_scheme :=
  | FORALL; names = list(LIDENT); COMMA; ~ = ty; { Ast.Forall(names, ty) }
  | ~ = ty; { Ast.Forall([], ty) }

let ty :=
  | l = ty1; ARROW; r = ty; { Ast.{ node = Ast.Arrow(l, r) } }
  | ty1

let ty1 :=
  | ty2

let ty2 :=
  | tcon = ty2; targ = ty3; { Ast.{ node = Ast.TyApp(tcon, targ) } }
  | ty3

let ty3 :=
  | UNIT; { Ast.{ node = Unit } }
  | name = LIDENT; { Ast.{ node = TyVar name } }
  | LPAREN; ~ = ty; RPAREN; { ty }

let expr :=
  | FUN; option(BAR); clauses = separated_list(BAR, clause);
    { Ast.{ node = Ast.Lam clauses } }
  | expr1

let expr1 :=
  | head = expr1; arg = expr2; { Ast.{ node = Ast.App(head, arg) } }
  | expr2

let expr2 :=
  | LPAREN; RPAREN; { Ast.{ node = Trivial } }
  | name = LIDENT; { Ast.{ node = Var name } }
  | LPAREN; ~ = expr; RPAREN; { expr }

let clause :=
  | pat = pat1; pats = list(pat1); ARROW; rhs = expr;
    { Ast.{ lhs = (pat, pats); rhs } }

let pat :=
  | name = UIDENT; pats = list(pat); { Ast.{ node = Ast.ConPat(name, pats) } }
  | pat1

let pat1 :=
  | LPAREN; RPAREN; { Ast.{ node = TrivialPat } }
  | name = LIDENT; { Ast.{ node = Ast.VarPat name } }
  | UNDERSCORE; { Ast.{ node = Ast.WildPat } }
  | LPAREN; ~ = pat; RPAREN; { pat }

%%
