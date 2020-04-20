{
open Parser

let keywords = Hashtbl.create 23
let () =
  List.iter (fun (k, v) -> Hashtbl.add keywords k v)
    [ "data", DATA
    ; "def", DEF
    ; "forall", FORALL
    ; "fun", FUN ]
}

let whitespace = [' ' '\t']
let digit = ['0'-'9']
let upper = ['A'-'Z']
let lower = ['a'-'z']
let alphanum = upper | lower | digit
let uident = upper (alphanum | '_' | '\'')*
let lident = lower (alphanum | '_' | '\'')*
let integer = ('-' | '+')? digit+
let decimal = integer ('.' digit+)

rule main = parse
  | whitespace { main lexbuf }
  | '\n' { Lexing.new_line lexbuf; main lexbuf }
  | '(' { LPAREN }
  | ')' { RPAREN }
  | '|' { BAR }
  | ':' { COLON }
  | ',' { COMMA }
  | '=' { EQUALS }
  | '_' { UNDERSCORE }
  | "->" { ARROW }
  | uident as str { UIDENT str }
  | lident as str {
    match Hashtbl.find_opt keywords str with
    | Some kw -> kw
    | None -> LIDENT str
    }
  | eof { EOF }
