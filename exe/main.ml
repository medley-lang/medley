(*open Medley

(* Must eta-expand state monad for let-generalization to kick in *)
let rec loop state =
  (let open Elab.Monad in
   let command = read_line () in
   Elab.catch
     (match command with
      | "apply" ->
         let* () = Elab.solve Elab.apply in
         let* focus = Elab.get_focus in
         print_string "Goal: ";
         print_endline (Term.print_ty 0 focus.Term.expected_ty);
         loop
      | "trivial" ->
         let* () = Elab.solve Elab.trivial in
         let* focus = Elab.get_focus in
         print_string "Goal: ";
         print_endline (Term.print_ty 0 focus.Term.expected_ty);
         loop
      | "quit" ->
         return ()
      | _ -> Elab.throw Error.UnknownTac)
     (function
      | Error.Done ->
         print_endline "Done";
         return ()
      | Error.IntroTac ->
         print_endline "Apply error";
         loop
      | Error.TrivialTac ->
         print_endline "Trivial error";
         loop
      | Error.UnknownTac ->
         print_endline "Unknown tactic";
         loop
      | _ ->
         print_endline "Other error";
         loop
  )) state

let () =
  print_endline "Enter a type:";
  let line = read_line () in
  let lexbuf = Lexing.from_string line in
  match
    Lexer.handle_errs "stdin" lexbuf Parser.Incremental.toplevel_ty_scheme
  with
  | Error _ ->
     print_endline "Parse failure"
  | Ok (Ast.Forall(_, ty)) ->
     match Elab.from_ast_ty ty with
     | Error _ ->
        print_endline "Elaboration failure"
     | Ok ty ->
        let hole =
          { Term.parent = Term.Root
          ; preterm = Term.Hole 0
          ; tctx = Context.create ()
          ; expected_ty = ty }
        in
        print_string "Goal: ";
        print_endline (Term.print_ty 0 ty);
        let (result, _) = loop (Elab.empty_state hole) in
        match result with
        | Ok _-> ()
        | Error _ -> print_endline "Failed"
 *)
