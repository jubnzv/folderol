(** The [Infer] module contains all the logic that handles rules and goals. *)

open IStd
open Syntax

(** Prefix used when generating new symbols. *)
let sym_prefix = "a"

let rec replace_term (u, new_) tm =
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
    abstraction, for example: *)
let subst_bound tm =
  let rec impl i (* next De Brujin index *) = function
    | Pred (p, tms) -> Pred (p, List.map tms ~f:(replace_term (tm, Bound i)))
    | Conn (c, fs) ->
        (* TODO: Which indexes will have connectives with the same lhs and rhs
                 (e.g. [X ∧ X])? *)
        Conn (c, List.map fs ~f:(impl i))
    | Quant (q, var, f) -> Quant (q, var, impl (i + 1) f)
  in
  impl 0

let rec accumulate f lhs rhs =
  match (lhs, rhs) with [], y -> y | x :: xs, y -> accumulate f xs (f x y)

let rec vars_in_term tm bs =
  match tm with
  | Var name -> if List.mem bs name ~equal:String.equal then bs else name :: bs
  | Fun (_, ts) -> accumulate vars_in_term ts bs
  | _ -> bs

(** Accumulate over all terms in a formula. *)
let rec accumulate_form f form bs =
  match form with
  | Pred (_, ts) -> accumulate f ts bs
  | Conn (_, fs) -> accumulate (accumulate_form f) fs bs
  | Quant (_, _, a) -> accumulate_form f a bs

let vars_in_form = accumulate_form vars_in_term

(** Represents a rule used in goals. *)
module Rule = struct
  (** The [side] type describes two parts of a formula.
    Formulas represented by this way: [Γ |− ∆]. This means: "if every formula
    in Γ is true then some formula in ∆ is true.". *)
  type side = Left  (** [Γ] *) | Right  (** [∆] *)

  let side_to_string = function Left -> "left" | Right -> "right"

  type t = {
    e_cost : int;  (** Cost is a number of premises the rule has *)
    e_side : side;
        (** Side of the rule means which set it represents ([Γ] or [∆]) *)
    e_formula : formula;
  }

  let to_string ?(formula_only = true)
      { e_cost = cost; e_side = side; e_formula = f } =
    if formula_only then Syntax.formula_to_string f
    else
      Printf.sprintf "%s (side: %s, cost: %d)"
        (Syntax.formula_to_string f)
        (side_to_string side) cost

  let cost r = r.e_cost
  let set_cost r c = { r with e_cost = c }
  let side r = r.e_side
  let set_side r s = { r with e_side = s }
  let formula r = r.e_formula
  let set_formula r f = { r with e_formula = f }

  (** Returns the cost of rule elements that depends on how many subgoals will
    be generated when applying the rule. *)
  let cost side formula =
    match (side, formula) with
    | _, Conn (CNeg, _) -> 1
    | Left, Conn (CConj, _) -> 1
    | Right, Conn (CDisj, _) -> 1
    | Right, Conn (CImpl, _) -> 1
    | Right, Quant (Forall, _, _) -> 1
    | Left, Quant (Exists, _, _) -> 1
    | Right, Conn (CConj, _) -> 2
    | Left, Conn (CDisj, _) -> 2
    | Left, Conn (CImpl, _) -> 2
    | _, Conn (CEq, _) -> 2
    | Left, Quant (Forall, _, _) -> 3
    | Right, Quant (Exists, _, _) -> 3
    | _ -> 4

  (** Constructs an rule from [side] and [formula]. *)
  let mk side formula =
    { e_cost = cost side formula; e_side = side; e_formula = formula }

  (** Compares costs of [lhs] and [rhs] rules using the comparison function
      [comp]. *)
  let cmp comp (lhs : t) (rhs : t) = comp lhs.e_cost rhs.e_cost

  let less = cmp ( < )
  let lesseq = cmp ( <= )
end

module Goal = struct
  type t = Rule.t list
  (** Goal is a list of rules that form [Γ] and [∆] depending on
      [Rule.e_side]. They are sorted by [e_cost] and should be added using
      only the [Rule.insert] functions. *)

  (** Inserts rule to the goal keeping rules sorted by their cost. *)
  let rec insert less x (g : t) : t =
    match (x, g) with
    | x, [] -> [ x ]
    | x, y :: ys -> if less y x then y :: insert less x ys else x :: y :: ys

  let insert_early = insert Rule.less
  let insert_late = insert Rule.lesseq
  let mk (rules : Rule.t list) : t = rules

  (** Creates an empty goal. *)
  let mk_empty () = mk []

  let to_string g =
    let rules_list_to_string xs =
      List.map xs ~f:Rule.to_string |> String.concat ~sep:", "
    in
    let lhs, rhs =
      List.partition_tf g ~f:(fun rule ->
          match Rule.side rule with Left -> true | Right -> false)
    in
    let list_str sym xs =
      if not @@ List.is_empty xs then
        Printf.sprintf "%s (%d): [%s]" sym (List.length xs)
          (rules_list_to_string xs)
      else ""
    in
    [ list_str "Г" lhs ] @ [ list_str "∆" rhs ] |> String.concat ~sep:"\n"

  (** Creates a subgoal adding to the goal [g]. It takes a list of pairs [side]
      and [formula] creating new rules from them, assigning their cost. *)
  let mk_subgoal (g : t) (pairs : (Rule.side * formula) list) =
    accumulate insert_early
      (List.map pairs ~f:(fun (side, f) -> Rule.mk side f))
      g

  (** Forms a list of subgoals from a goal adding rules generated from
      [pairlist] to it. *)
  let mk_subgoals (g : t) (pairslist : (Rule.side * formula) list list) =
    List.map pairslist ~f:(mk_subgoal g)

  (** Splits the rules in the goal generating corresponding lists for [Γ] and [∆]. *)
  let split (g : t) =
    let rec split left right = function
      | [] -> (left, right)
      | rule :: rules -> (
          let f = Rule.formula rule in
          match Rule.side rule with
          | Left -> split (f :: left) right rules
          | Right -> split left (f :: right) rules)
    in
    split [] [] (List.rev g)

  (** Solves the goal [g].
      Solving means comparing each atomic formula from [Γ] and [∆] and trying
      to unify each right formula with the left one.
      On success it returns a list of simplified formulas and updated
      environments we got after unifying these. *)
  let solve (g : t) =
    let rec find_left left right =
      match left with
      | [] -> [] (* failure *)
      | l :: ls -> find_right l ls right
    and find_right l_cur left right =
      match right with
      | [] -> find_left left right
      | r :: rs -> (
          let open Unify in
          match unify (Env.mk ()) l_cur r with
          | Ok env' -> [ (l_cur, env') ]
          | Error _ -> find_right l_cur left rs)
    in
    let left, right = split g in
    find_left (List.filter left ~f:is_pred) (List.filter right ~f:is_pred)

  (** Accumulates all formulae in a goal. *)
  let rec accumulate_goal f (g : t) bs =
    match g with
    | [] -> bs
    | rule :: rules -> accumulate_goal f rules (f (Rule.formula rule) bs)

  (** Return variables from the goal [g]. *)
  let vars_in_goal = accumulate_goal vars_in_form

  let gensym =
    let n = ref (-1) in
    fun () ->
      incr n;
      Printf.sprintf "%s%d" sym_prefix !n

  (** Reduces all the rules creating the immediate subformula to build
      subgoals. *)
  let reduce (g : t) (r : Rule.t) =
    let mk_subgoals' = mk_subgoals g in
    let vars_in a = vars_in_goal g (vars_in_form a []) in
    let subparam a = subst_bound (Param (gensym (), vars_in a)) a in
    let subvar a = subst_bound (Var (gensym ())) a in
    match (Rule.side r, Rule.formula r) with
    | Right, Conn (CNeg, [ a ]) -> Ok (mk_subgoals' [ [ (Left, a) ] ])
    | Left, Conn (CNeg, [ a ]) -> Ok (mk_subgoals' [ [ (Right, a) ] ])
    | Right, Conn (CConj, a :: [ b ]) ->
        Ok (mk_subgoals' [ [ (Right, a) ]; [ (Right, b) ] ])
    | Left, Conn (CConj, a :: [ b ]) ->
        Ok (mk_subgoals' [ [ (Left, a); (Left, b) ] ])
    | Right, Conn (CDisj, a :: [ b ]) ->
        Ok (mk_subgoals' [ [ (Right, a); (Right, b) ] ])
    | Left, Conn (CDisj, a :: [ b ]) ->
        Ok (mk_subgoals' [ [ (Left, a) ]; [ (Left, b) ] ])
    | Right, Conn (CImpl, a :: [ b ]) ->
        Ok (mk_subgoals' [ [ (Left, a); (Right, b) ] ])
    | Left, Conn (CImpl, a :: [ b ]) ->
        Ok (mk_subgoals' [ [ (Right, a) ]; [ (Left, b) ] ])
    | Right, Conn (CEq, a :: [ b ]) ->
        Ok
          (mk_subgoals'
             [ [ (Left, a); (Right, b) ]; [ (Right, a); (Left, b) ] ])
    | Left, Conn (CEq, a :: [ b ]) ->
        Ok
          (mk_subgoals'
             [ [ (Left, a); (Left, b) ]; [ (Right, a); (Right, b) ] ])
    | Right, Quant (Forall, _, a) ->
        Ok (mk_subgoals' [ [ (Right, subparam a) ] ])
    | Left, Quant (Forall, _, a) ->
        Ok [ insert_early (Rule.mk Left @@ subvar a) (insert_late r g) ]
    | Right, Quant (Exists, _, a) ->
        Ok [ insert_early (Rule.mk Right @@ subvar a) (insert_late r g) ]
    | Left, Quant (Exists, _, a) -> Ok (mk_subgoals' [ [ (Left, subparam a) ] ])
    | _ ->
        Error
          (Printf.sprintf "Cannot reduce goal (formula: %s side: %s)"
             (formula_to_string @@ Rule.formula r)
             (Rule.side_to_string @@ Rule.side r))
end

module Goaltable = struct
  type t = Goal.t list

  (** Creates the initial goal table that contains only a single goal
      constructed from the given formulas. *)
  let mk (lhs : formula list) (rhs : formula list) : t =
    let mk_goals side = List.map ~f:(fun f -> Rule.mk side f) in
    [ Goal.mk @@ mk_goals Rule.Left lhs @ mk_goals Rule.Right rhs ]

  let rec inst_term env = function
    | Fun (name, ts) -> Fun (name, List.map ts ~f:(inst_term env))
    | Var name ->
        Unify.Env.lookup env name
        |> Option.value_map ~default:(Var name) ~f:(fun assigned_term ->
               (* Recursive call here is necessary, otherwise the result is
                  [?name]. *)
               inst_term env assigned_term)
    (* | Param (name, var_names) -> Param (name, accumulate vars_in_term (List.map) var_names) *)
    | t -> t

  let rec inst_form env f =
    if Unify.Env.is_empty env then f
    else
      match f with
      | Pred (name, ts) -> Pred (name, List.map ts ~f:(inst_term env))
      | Conn (c, fs) -> Conn (c, List.map fs ~f:(inst_form env))
      | Quant (q, var, f) -> Quant (q, var, inst_form env f)

  let rec inst_goal env g =
    match g with
    | [] -> []
    | rule :: g ->
        let f' = inst_form env (Rule.formula rule) in
        Rule.set_formula rule f' :: inst_goal env g

  let inst_goals env gs =
    if Unify.Env.is_empty env then gs else List.map gs ~f:(inst_goal env)

  (** Inserts goals [goals] to the goal table [gt]. Before insertion it tries
      to solve each new goal. *)
  let rec insert_goals (goals : Goal.t list) (success_formulas : formula list)
      (gt : t) =
    match goals with
    | [] -> (success_formulas, gt)
    | g :: gs -> (
        match Goal.solve g with
        | (left_formula, env) :: _ ->
            (* After solving a goal, we have to instantiate all the other
               goals with the resulting environment, since its variables may
               appear in other goals. *)
            let goals' = inst_goals env gs
            and success_formulas' =
              inst_form env left_formula :: success_formulas
            and gt' = inst_goals env gt in
            insert_goals goals' success_formulas' gt'
        | [] -> insert_goals gs success_formulas (g :: gt))

  let to_string (gt : t) =
    List.map gt ~f:Goal.to_string |> String.concat ~sep:"-----\n"

  (** Prints the rule used, with each formula found by unification. *)
  let print_step (rule : Rule.t) (num_goals : int) vars =
    Printf.printf "%s%s(%s): [%s]\n"
      (String.init num_goals ~f:(fun _ -> ' '))
      (formula_to_string @@ Rule.formula rule)
      (Rule.side_to_string @@ Rule.side rule)
      (List.map vars ~f:(fun f -> formula_to_string f)
      |> String.concat ~sep:", ")

  (** Reduces the first rule in the goals table and replaces it with the
      subgoals creating a new goal table. *)
  let proof_step (gt : t) =
    match gt with
    | [] -> Ok []
    | [] :: _tab -> Error "Empty goal"
    | (rule :: (goal : Goal.t)) :: tab ->
        let%bind subgoals = Goal.reduce goal rule in
        let ss, gt' = insert_goals subgoals [] tab in
        print_step rule (List.length tab) ss;
        Ok gt'

  let rec proof_steps num_steps (gt : t) =
    if phys_equal 0 num_steps then Ok gt
    else
      match gt with
      | [] -> Ok []
      | tab ->
          let%bind gt' = proof_step tab in
          proof_steps (num_steps - 1) gt'
end
