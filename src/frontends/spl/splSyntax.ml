(** SPL abstract syntax. *)

open Form

type idents = ident list

type pos = source_position

type name = string

type names = name list

type typ =
  | StructType of ident
  | FieldType of ident * typ
  | SetType of typ
  | IntType
  | BoolType
  | LocType
  | UniversalType
  (*| ArrayType of typ*)

type var_decl_id =
  | IdentDecl of ident
  | ArrayDecl of var_decl_id

type op = 
  | OpDiff | OpUn | OpInt 
  | OpMinus | OpPlus | OpMult | OpDiv 
  | OpEq | OpNeq | OpGt | OpLt | OpGeq | OpLeq | OpIn
  | OpPts | OpSepStar | OpSepPlus | OpSepWand | OpSepIncl
  | OpAnd | OpOr | OpImpl | OpNot 

type quantifier_kind =
  | Forall | Exists

type compilation_unit =
    { package : name option;
      imports : names;
      var_decls : vars;
      struct_decls : structs;
      proc_decls : procs;
      pred_decls : preds;
    }

and decl =
  | VarDecl of var
  | ProcDecl of proc
  | PredDecl of pred
  | StructDecl of struc

and decls = decl list

and proc =
    { p_name : ident;
      p_formals : idents;
      p_returns : idents;
      p_locals : vars;
      p_contracts : proc_contracts;
      p_body : stmt; 
      p_pos : pos;
    }

and procs = proc IdMap.t

and pred =
    { pr_name : ident;
      pr_formals : idents;
      pr_locals : vars;
      pr_body : expr; 
      pr_pos : pos;
    }

and preds = pred IdMap.t

and var =
    { v_name : ident;
      v_type : typ; 
      v_ghost : bool;
      v_implicit : bool;
      v_aux : bool;
      v_pos : pos;
    }

and vars = var IdMap.t

and proc_contract =
  | Requires of expr
  | Ensures of expr

and proc_contracts = proc_contract list

and struc =
    { s_name : ident;
      s_fields : vars;
      s_pos : pos;
    }

and structs = struc IdMap.t

and stmt =
  | Skip of pos
  | Block of stmts * pos
  | LocalVars of var list * pos
  | Assume of expr * pos
  | Assert of expr * pos
  | Assign of exprs * exprs * pos
  | Havoc of exprs * pos
  | Dispose of expr * pos
  | If of expr * stmt * stmt * pos
  | Loop of loop_contracts * stmt * expr * stmt * pos
  | Return of exprs * pos

and stmts = stmt list

and loop_contracts = loop_contract list

and loop_contract = 
  | Invariant of expr

and expr =
  | Null of pos
  | Emp of pos
  | Setenum of typ * exprs * pos
  | IntVal of int * pos
  | BoolVal of bool * pos
  | New of ident * pos
  | Dot of expr * ident * pos
  | ProcCall of ident * exprs * pos
  | PredApp of ident * exprs * pos
  | Quant of quantifier_kind * var list * expr * pos
  | GuardedQuant of quantifier_kind * ident * expr * expr * pos
  | Access of expr * pos
  | BtwnPred of expr * expr * expr * expr * pos
  | UnaryOp of op * expr * pos
  | BinaryOp of expr * op * expr * pos
  | Ident of ident * pos

and exprs = expr list

let pos_of_expr = function
  | Null p 
  | Emp p 
  | IntVal (_, p) 
  | BoolVal (_, p)
  | Setenum (_, _, p)
  | New (_, p)
  | Dot (_, _, p)
  | Access (_, p)
  | BtwnPred (_, _, _, _, p)
  | Quant (_, _, _, p)
  | GuardedQuant (_, _, _, _, p)
  | ProcCall (_, _, p)
  | PredApp (_, _, p)
  | UnaryOp (_, _, p)
  | BinaryOp (_, _, _, p)
  | Ident (_, p) -> p
  
let pos_of_stmt = function
  | Skip pos
  | Block (_, pos)
  | LocalVars (_, pos)
  | Assume (_, pos)
  | Assert (_, pos)
  | Assign (_, _, pos)
  | Dispose (_, pos)
  | Havoc (_, pos)
  | If (_, _, _, pos)
  | Loop (_, _, _, _, pos)
  | Return (_, pos) -> pos

let proc_decl hdr body =
  { hdr with p_body = body }

let struct_decl sname sfields pos =
  { s_name = sname;  s_fields = sfields; s_pos = pos }

let var_decl vname vtype vghost vimpl vpos =
  { v_name = vname; v_type = vtype; v_ghost = vghost; v_implicit = vimpl; v_aux = false; v_pos = vpos } 

let compilation_unit pkg ims decls =
  let alloc_decl = VarDecl (var_decl Prog.alloc_id (SetType LocType) true false FormUtil.dummy_position) in
  let check_uniqueness id pos (vdecls, pdecls, prdecls, sdecls) =
    if IdMap.mem id vdecls || IdMap.mem id sdecls || IdMap.mem id pdecls || IdMap.mem id prdecls
    then ProgError.error pos ("redeclaration of identifier " ^ (fst id) ^ ".");
  in
  let vdecls, pdecls, prdecls, sdecls =
    List.fold_left (fun (vdecls, pdecls, prdecls, sdecls as decls) -> function
      | VarDecl decl -> 
          check_uniqueness decl.v_name decl.v_pos decls;
          IdMap.add decl.v_name decl vdecls, pdecls, prdecls, sdecls
      | ProcDecl decl -> 
          check_uniqueness decl.p_name decl.p_pos decls;
          vdecls, IdMap.add decl.p_name decl pdecls, prdecls, sdecls
      | PredDecl decl -> 
          check_uniqueness decl.pr_name decl.pr_pos decls;
          vdecls, pdecls, IdMap.add decl.pr_name decl prdecls, sdecls
      | StructDecl decl -> 
          check_uniqueness decl.s_name decl.s_pos decls;
          vdecls, pdecls, prdecls, IdMap.add decl.s_name decl sdecls)
      (IdMap.empty, IdMap.empty, IdMap.empty, IdMap.empty)
      (alloc_decl :: decls)
  in
  { package = pkg; 
    imports = ims; 
    var_decls = vdecls; 
    struct_decls = sdecls; 
    proc_decls = pdecls;
    pred_decls = prdecls;
  }


let mk_block pos = function
  | [] -> Skip pos
  | [stmt] -> stmt
  | stmts -> Block (stmts, pos)

