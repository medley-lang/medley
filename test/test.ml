open Medley

let test_pass filename =
  let chan = open_in filename in
  Fun.protect (fun () ->
      let lexbuf = Lexing.from_channel chan in
      Lexer.handle_errs filename lexbuf Parser.Incremental.program
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
