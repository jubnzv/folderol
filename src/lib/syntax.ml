open IStd

type term =
  | Var of string  (** [Var(N)] is a meta-variable. *)
  | Param of string * string list
      (** [Param(N, Vars)] is a parameter named [N] with variables [Vars]
        representing provisos of quantifier rules. Proviso is a limitation
        when a quantifier rule can be used. An example of proviso could be the
        following: [∀x(P(x) ∨ Q(x)) ⇔ (∀x P(x)) ∨ (∀x Q(x)) ,
        (proviso: x is not free in the other quantified variable)]. *)
  | Bound of int
      (** [Bound(Idx)] are bound variables that have De Brujin indexes ([Idx])
        instead names. *)
  | Fun of string * term list
      (** [Fun(N, Args)] is a function with name [N] and arguments
          [Args]. *)
[@@deriving eq]

type quant = Forall  (** ∀ *) | Exists  (** ∃ *) [@@deriving eq]

(** Propositional logic connectives *)
type conn =
  | CConj  (** ∧ *)
  | CDisj  (** ∨ *)
  | CImpl  (** → *)
  | CEq  (** ↔ *)
  | CNeg  (** ¬ *)
[@@deriving eq]

type formula =
  | Pred of string * term list
      (** [Pred(P, Ti)] is an atomic formula where [P] is an n-place predicate
        symbol and [Ti] are terms present by the name of the predicate and
        the list of its arguments. For example, in the [P(x1, x2)] formula
        [P] is an arbitrary non-logical symbol that have its own mean and
        [x1] and [x2] are its arguments. 0-place function symbols are
        constants. *)
  | Conn of conn * formula list
      (** [Conn(C, Forms)] is a formula with connective [C] and the list of
        formulas [Forms]. Negation is represented as an
        unary [¬A]. *)
  | Quant of quant * string * formula
      (** [Quant(Q, Var, Form)] is a quantified formula with quantifier [Q],
        bound variable [Var] and the body [Form]. *)
[@@deriving eq]

let is_pred = function Pred _ -> true | _ -> false

let rec term_to_string = function
  | Var n -> "?" ^ n
  | Param (n, vars) when List.is_empty vars -> Printf.sprintf "%s" n
  | Param (n, vars) ->
      List.map vars ~f:(Caml.String.cat "?")
      |> String.concat ~sep:", " |> Printf.sprintf "%s(%s)" n
  | Bound idx -> Printf.sprintf "%d" idx
  | Fun (n, args) ->
      List.map args ~f:term_to_string
      |> String.concat ~sep:", " |> Printf.sprintf "%s(%s)" n

let quant_to_string = function Forall -> "∀" | Exists -> "∃"

let conn_to_string = function
  | CConj -> "∧"
  | CDisj -> "∨"
  | CImpl -> "→"
  | CEq -> "↔"
  | CNeg -> "¬"

let rec formula_to_string = function
  | Pred (p, args) ->
      List.map args ~f:term_to_string
      |> String.concat ~sep:", " |> Printf.sprintf "%s(%s)" p
  | Conn (c, fs) when List.is_empty fs ->
      Printf.sprintf "<broken connective: %s>" (conn_to_string c)
  | Conn (c, fs) when phys_equal 1 @@ List.length fs ->
      Printf.sprintf "%s%s" (conn_to_string c)
        (formula_to_string (List.hd_exn fs))
  | Conn (c, fs) ->
      let sep = Printf.sprintf " %s " (conn_to_string c) in
      List.map fs ~f:formula_to_string |> String.concat ~sep
  | Quant (q, v, f) ->
      Printf.sprintf "%s%s.%s" (quant_to_string q) v (formula_to_string f)

let%test "formula_to_string_works_1" =
  let f1 =
    Quant (Forall, "x", Quant (Forall, "y", Pred ("P", [ Param ("x", []) ])))
  in
  String.equal "∀x.∀y.P(x)" (formula_to_string f1);
