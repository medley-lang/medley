{
open Parser

let keywords = Hashtbl.create 23
let () =
  List.iter (fun (k, v) -> Hashtbl.add keywords k v)
    [ "data", DATA
    ; "def", DEF
    ; "forall", FORALL
    ; "fun", FUN
    ; "unit", UNIT ]
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

{
module I = Parser.MenhirInterpreter

let handle_errs filename lexbuf parser =
  let succeed a = Ok a in
  let fail _ =
    Result.Error
      (filename, Lexing.lexeme_start_p lexbuf, Lexing.lexeme_end_p lexbuf)
  in
  let supplier = I.lexer_lexbuf_to_supplier main lexbuf in
  I.loop_handle succeed fail supplier (parser lexbuf.Lexing.lex_curr_p)

}
