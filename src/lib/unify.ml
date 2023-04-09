open IStd
open Syntax

module Env : sig
  type variable_name = string
  type t

  val mk : unit -> t
  (** Creates a new environment. *)

  val is_empty : t -> bool
  (** Returns [true] iff [env] is an empty environment. *)

  val to_string : t -> string
  (** Prints the environment. *)

  val add : t -> variable_name -> term -> t
  (** Adds [variable_name] mapped to [term_name]. *)

  val lookup : t -> variable_name -> term option
  (** Looks up a variable [var_name] in the environment. *)
end = struct
  type variable_name = string
  type t = (variable_name * term) list

  let mk () : t = []
  let is_empty = List.is_empty

  let to_string env =
    List.fold_left env ~init:[] ~f:(fun acc (var_name, term) ->
        acc @ [ Printf.sprintf "%s = %s" var_name (term_to_string term) ])
    |> String.concat ~sep:"\n"

  let add (env : t) var_name tm = (var_name, tm) :: env

  let rec lookup (env : t) var_name =
    if List.is_empty env then None
    else
      let v, t = List.hd_exn env in
      if String.equal v var_name then Some t
      else lookup (List.tl_exn env) var_name
end

(** Chases variable assignments, replacing the argument, if a variable, by its
    assignment. For example, if [env] contains [?a → ?b] and [?c → ?b] then
    [chase_var] will map [?a] to [?c]. Basically, that's the recursive search
    in the environment. *)
let rec chase_var env = function
  | Var var_name ->
      Env.lookup env var_name
      |> Option.value_map ~default:(Var var_name) ~f:(chase_var env)
  | tm -> tm

(** Unifies two terms [t] and [u] with the environment [env].
    All the terms may be unified, except bound variables ([Bound]).  *)
let rec unify_term (env : Env.t) (t : term) (u : term) : (Env.t, string) result
    =
  match (t, u) with
  | Var a, t | t, Var a ->
      (* TODO: Is that correct for both branches? Should we change the
               positions of arguments? *)
      unify_var env (chase_var env (Var a)) (chase_var env t)
  | Param (a, _), Param (b, _) ->
      if String.equal a b then Ok env
      else
        Error
          (Printf.sprintf
             "Cannot unify parameter terms with different names: %s and %s" a b)
  | Fun (a, ts), Fun (b, us) ->
      if String.equal a b then unify_terms env ts us
      else
        Error
          (Printf.sprintf
             "Cannot unify function terms with different names: %s and %s" a b)
  | t, u ->
      Error
        (Printf.sprintf "Cannot unify terms with types %s and %s"
           (term_to_string t) (term_to_string u))

(** Unifies the variable [var] with the term [t]. If [var] is assigned to the
    term [t], this binding will be added to the environment. *)
and unify_var (env : Env.t) (var : term) (t : term) : (Env.t, string) result =
  (* Searches the occurrence of variable named [target] in the given term. *)
  let rec occs target = function
    | Fun (_, ts) -> occsl target ts
    | Param (_, var_names) ->
        occsl target (List.map var_names ~f:(fun name -> Var name))
    | Var name ->
        if String.equal name target then true
        else
          Env.lookup env name
          |> Option.value_map ~default:false ~f:(fun assigned_term ->
                 occs target assigned_term)
    | _ -> false
  and occsl target ts = List.find ~f:(occs target) ts |> Option.is_some in

  match (var, t) with
  | Var a, t when equal_term (Var a) t -> Ok env
  | Var a, t ->
      if occs a t then
        Error
          (Printf.sprintf "Variable %s already assigned in the environment" a)
      else Ok (Env.add env a t)
  | t, u -> unify_term env t u

(** Unifies two lists of terms [ts] and [us] in the environment [env], one at
      time. *)
and unify_terms (env : Env.t) (ts : term list) (us : term list) =
  let rec unify_terms_impl env ts us =
    match (ts, us) with
    | [], [] -> Ok env
    | t :: ts, u :: us ->
        let%bind env' = unify_term env t u in
        unify_terms_impl env' ts us
    | _ -> Error "Cannot unify lists of terms with the different length"
  in
  unify_terms_impl env ts us

let unify (env : Env.t) (t : formula) (u : formula) : (Env.t, string) result =
  match (t, u) with
  | Pred (a, ts), Pred (b, us) when String.equal a b -> unify_terms env ts us
  | _ ->
      Error
        (Printf.sprintf
           "Unification supports only atomic formulas but the following are \
            given: %s and %s"
           (formula_to_string t) (formula_to_string u))

let%test "unify_works_1" =
  let f2 = Pred ("f", [ Param ("a", []); Param ("b", []) ])
  and f3 = Pred ("f", [ Var "a"; Var "b" ]) in
  let env = Env.mk () in
  match unify env f2 f3 with
  | Ok env' ->
      String.equal "b = b\na = a" (Env.to_string env')
  | Error err -> (
    Printf.printf "Unification error: %s\n" err;
    false)
