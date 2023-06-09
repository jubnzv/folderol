open FolderolLib
open IStd

let usage_string =
  Printf.sprintf
    "Usage: %s [FILENAME]\nRunning without arguments launches the REPL session"
    Caml.Sys.argv.(0)

(** Runs interactive REPL *)
let run_repl () = failwith "run_repl: NYI"

let parse_file f =
  In_channel.with_file f ~f:(fun inx ->
      let lexbuf = Lexing.from_channel inx in
      let l = Lexer.initial in
      try Parser.main l lexbuf with e -> Error (Exn.to_string e))

let run_file f =
  let%bind gt = parse_file f in
  Driver.init gt;
  Driver.run ();
  Ok ()

let handle_error = function
  | Ok _ -> exit 0
  | Error msg ->
      Printf.eprintf "Error: %s\n" msg;
      exit 1

let () =
  let args = Caml.Sys.argv in
  match Array.to_list args with
  | [ _ ] -> run_repl ()
  | _ :: [ f ] when String.equal "-" f -> run_repl ()
  | _ :: [ f ] -> run_file f |> handle_error
  | _ -> failwith usage_string
