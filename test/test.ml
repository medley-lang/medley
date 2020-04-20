open Medley
module I = Parser.MenhirInterpreter

let handle_errs filename lexbuf =
  let succeed a = Ok a in
  let fail _ =
    Error (filename, Lexing.lexeme_start_p lexbuf, Lexing.lexeme_end_p lexbuf)
  in
  let supplier = I.lexer_lexbuf_to_supplier Lexer.main lexbuf in
  I.loop_handle succeed fail supplier

let test_pass filename =
  let chan = open_in filename in
  Fun.protect (fun () ->
      let lexbuf = Lexing.from_channel chan in
      handle_errs filename lexbuf
        (Parser.Incremental.program lexbuf.Lexing.lex_curr_p)
    ) ~finally:(fun () ->
      close_in chan
    )

let () =
  let errs =
    List.fold_right (fun name errs ->
        match test_pass name with
        | Ok _ -> errs
        | Error e -> e :: errs
      )
      ["pass/id.med"] []
  in
  match errs with
  | [] -> ()
  | errs ->
     List.iter (fun (filename, _start, _ending) ->
         print_endline filename
       ) errs;
     exit 1
