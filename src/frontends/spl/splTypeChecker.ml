open Grass
open SplSyntax

(** Computes SPL type of expression [e] in compilation unit [cu] and environment [locals].
  * Assumes that all identifiers in [e] have been resolved. *)
let type_of_expr cu locals e = 
  let rec te = function
    (* Bool return values *)
    | UnaryOp (OpNot, _, _)
    | BinaryOp (_, OpAnd, _, _)
    | BinaryOp (_, OpOr, _, _)
    | BinaryOp (_, OpImpl, _, _)
    | BinaryOp (_, OpEq, _, _)
    | BinaryOp (_, OpNeq, _, _)
    | BinaryOp (_, OpGt, _, _)
    | BinaryOp (_, OpLt, _, _)
    | BinaryOp (_, OpGeq, _, _)
    | BinaryOp (_, OpLeq, _, _)
    | BinaryOp (_, OpIn, _, _)
    | GuardedQuant _ 
    | Quant _
    | PredApp _ 
    | BoolVal _ -> BoolType
    (* Int return values *)
    | UnaryOp (OpMinus, _, _) 
    | BinaryOp (_, OpMinus, _, _)
    | BinaryOp (_, OpPlus, _, _)
    | BinaryOp (_, OpMult, _, _)
    | BinaryOp (_, OpDiv, _, _)
    | IntVal _ -> IntType
    (* Set return values *)
    | BinaryOp (e, OpDiff, _, _)
    | BinaryOp (e, OpUn, _, _)
    | BinaryOp (e, OpInt, _, _) ->
        te e
    | Setenum (ty, _, _) ->
        SetType ty
    (* Struct types *)
    | New (id, _) ->
        StructType id
    | Dot (_, id, _) ->
        let decl = IdMap.find id cu.var_decls in
        (match decl.v_type with
        | MapType (_, ty) -> ty
        | _ -> UniversalType)
    (* Other stuff *)
    | Null _ -> LocType
    | ProcCall (id, _, _) ->
        let decl = IdMap.find id cu.proc_decls in
        (match decl.p_returns with
        | [rid] -> 
            let rdecl = IdMap.find rid decl.p_locals in
            rdecl.v_type
        | _ -> UniversalType)
    | Ident (id, _) ->
        let decl = 
          try
            IdMap.find id locals
          with Not_found ->
            IdMap.find id cu.var_decls
        in
        decl.v_type
    | Annot (e, _, _) ->
        te e
    | _ -> UniversalType
  in 
  te e
  
