open IStd

(** The global goal table. *)
let g_goaltable = ref ([] : Infer.Goaltable.t)

(** Sets the global tab. *)
let set_tab ?(print = true) tab =
  g_goaltable := tab;
  if print then Printf.printf "%s\n" @@ Infer.Goaltable.to_string tab

let clear_tab () = set_tab []

(** A helper functions that unwraps possible errors occurred during execution. *)
let run_steps f gt =
  match f gt with
  | Ok gt' -> set_tab gt'
  | Error msg ->
      Printf.eprintf "%s\n" msg;
      clear_tab ()

let init gt = set_tab gt
let step () = run_steps Infer.Goaltable.proof_step !g_goaltable
let steps n = run_steps (Infer.Goaltable.proof_steps (Int.max 0 n)) !g_goaltable
let run () = run_steps (Infer.Goaltable.proof_steps Int.max_value) !g_goaltable
