open Core

let rec replace_term (u, new_) tm =
  let open Syntax in
  if equal_term u tm then new_
  else
    match tm with
    | Fun (name, args) -> Fun (name, List.map args ~f:(replace_term (u, new_)))
    | _ -> tm

(** Abstraction maps A to ∀x.A[x/t] (or ∃x.A[x/t]), replacing all occurrences
    of the term [tm] by the bound variable x.
    We need the abstraction to make the term follow the De Brujin notation.
    Basically, it eliminates all bound variable names replacing them with De
    Brujin indexes.

    Here are some examples:
    ∀x.∀y.P (x) =>  ∀∀P (1)
    ∀y.∀x.P (y) =>  ∀∀P (1)
    ∀x.∀y.P (y) =>  ∀∀P (0)
    ∀x.∀x.P (x) =>  ∀∀P (0)
    ∀x.∀y.P (a) =>  ∀∀P (a) *)
let abstract tm =
  let open Syntax in
  let rec impl i (* next De Brujin index *) = function
    | Pred (p, tms) -> Pred (p, List.map tms ~f:(replace_term (Bound i, tm)))
    | Conn (c, fs) ->
        (* TODO: Which indexes will have connectives with the same lhs and rhs
                 (e.g. [X ∧ X])? *)
        Conn (c, List.map fs ~f:(impl i))
    | Quant (q, var, f) -> Quant (q, var, impl (i + 1) f)
  in
  impl 0

(** Substitution maps ∀x.A (or ∃x.A) to A[t/x], replacing all occurrences of
    the bound variable x by the term [tm]. It reverses the result of
    abstraction, for example:
    *)
let subst_bound tm =
  let open Syntax in
  let rec impl i (* next De Brujin index *) = function
    | Pred (p, tms) -> Pred (p, List.map tms ~f:(replace_term (tm, Bound i)))
    | Conn (c, fs) ->
        (* TODO: Which indexes will have connectives with the same lhs and rhs
                 (e.g. [X ∧ X])? *)
        Conn (c, List.map fs ~f:(impl i))
    | Quant (q, var, f) -> Quant (q, var, impl (i + 1) f)
  in
  impl 0

let () =
  let open Syntax in
  let f1 =
    Quant (Forall, "x", Quant (Forall, "y", Pred ("P", [ Param ("x", []) ])))
  in
  (* ∀x.∀y.P(x) *)
  Printf.printf "%s\n" (formula_to_string f1)
