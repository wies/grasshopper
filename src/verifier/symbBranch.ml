(** {5 Symbolic execution inspired by Viper's Silicon} *)

open Stdlib
open SymbState
open GrassUtil
open Grass
open Prog 
open Printf
open Util

let rec branch_simple (state: symb_state) comms (fexec: symb_state -> Prog.command -> (symb_state -> vresult) -> vresult) fc : vresult =
  match comms with
  | [] -> Result.Ok [] 
  | comm :: comms' ->
      match fexec state comm fc with 
      | Result.Error err as e -> e 
      | Result.Ok _ -> branch_simple state comms' fexec fc
