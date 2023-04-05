open IStd
open Syntax

(** [Env] represents the environment for unification. *)
module Env : sig
  type variable_name = string
  type t

  val mk : unit -> t
  (** Creates a new environment. *)

  val to_string : t -> string
  (** Prints the environment. *)

  val add : t -> variable_name -> term -> t
  (** Adds [variable_name] mapped to [term_name]. *)

  val lookup : t -> variable_name -> term option
  (** Looks up a variable [var_name] in the environment. *)
end

val unify : Env.t -> formula -> formula -> (Env.t, string) result
(** Performs the unification of two formulas [f1] and [f2] in the environment
    [env].

    This means that we need to solve a set of equations from [ts] and [us] over
    the meta-variables in the terms. This equations are considered one at time.

    It returns an error if lengths of the lists are differ.
 *)
