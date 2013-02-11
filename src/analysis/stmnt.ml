open Form
open FormUtil
open Axioms
open Config

type stmnt =
  | VarUpdate of ident * term
  | FunUpdate of ident * term * term
  | New of ident
  | Dispose of ident
  | Assume of form

type path = stmnt list

let ssa_partial ident_map path = failwith "deprecated"

let ssa_form path = fst (ssa_partial IdMap.empty path)
