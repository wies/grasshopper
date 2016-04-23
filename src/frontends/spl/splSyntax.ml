(** SPL abstract syntax. *)

open Grass

type idents = ident list

type pos = source_position

type name = string

type names = name list

type typ =
  | StructType of ident
  | MapType of typ * typ
  | ArrayType of typ
  | ArrayCellType of typ
  | SetType of typ
  | IntType
  | BoolType
  | ByteType
  | UnitType
  | AnyRefType
  | PermType (* SL formulas *)
  | AnyType

type var_decl_id =
  | IdentDecl of ident
  | ArrayDecl of var_decl_id

type spl_program =
    { includes : (name * pos) list;
      var_decls : vars;
      struct_decls : structs;
      proc_decls : procs;
      pred_decls : preds;
      background_theory : (expr * pos) list; 
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
      pr_footprints : idents;
      pr_outputs : idents;
      pr_locals : vars;
      pr_body : expr; 
      pr_is_footprint : bool;
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
      v_scope : pos;
    }

and vars = var IdMap.t

and proc_contract =
  | Requires of expr * bool
  | Ensures of expr * bool

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
  | LocalVars of var list * exprs option * pos
  | Assume of expr * bool * pos
  | Assert of expr * bool * pos
  | Assign of exprs * exprs * pos
  | Havoc of exprs * pos
  | Dispose of expr * pos
  | If of expr * stmt * stmt * pos
  | Loop of loop_contracts * stmt * expr * stmt * pos
  | Return of exprs * pos

and stmts = stmt list

and loop_contracts = loop_contract list

and loop_contract = 
  | Invariant of expr * bool

and bound_var =
  | GuardedVar of ident * expr
  | UnguardedVar of var

and expr =
  | Null of typ * pos
  | Emp of pos
  | Setenum of typ * exprs * pos
  | IntVal of Int64.t * pos
  | BoolVal of bool * pos
  | New of typ * exprs * pos
  | Read of expr * expr * pos
  | Old of expr * pos
  | Length of expr * pos
  | ArrayOfCell of expr * pos
  | IndexOfCell of expr * pos
  | ArrayCells of expr * pos
  | ProcCall of ident * exprs * pos
  | PredApp of pred_sym * exprs * pos
  | Binder of binder_kind * bound_var list * expr * pos
  | UnaryOp of op * expr * pos
  | BinaryOp of expr * op * expr * typ * pos
  | Ident of ident * pos
  | Annot of expr * annotation * pos

and exprs = expr list

and op = 
  | OpDiff | OpUn | OpInt 
  | OpMinus | OpPlus | OpMult | OpDiv 
  | OpEq | OpGt | OpLt | OpGeq | OpLeq | OpIn
  | OpPts | OpSepStar | OpSepPlus | OpSepIncl
  | OpBvAnd | OpBvOr | OpBvNot | OpBvShiftL | OpBvShiftR | OpToInt | OpToByte
  | OpAnd | OpOr | OpImpl | OpNot 

and pred_sym =
  | AccessPred | BtwnPred | DisjointPred | FramePred | ReachPred | Pred of ident
      
and binder_kind =
  | Forall | Exists | SetComp

and annotation =
  | GeneratorAnnot of (expr * ident list) list * expr
  | PatternAnnot of expr
  | CommentAnnot of string

(** Utility functions *)
        
let pos_of_expr = function
  | Null (_, p) 
  | Emp p 
  | IntVal (_, p) 
  | BoolVal (_, p)
  | Setenum (_, _, p)
  | New (_, _, p)
  | Read (_, _, p)
  | Old (_, p)
  | Length (_, p)
  | ArrayOfCell (_, p)
  | IndexOfCell (_, p)
  | ArrayCells (_, p)
  | Binder (_, _, _, p)
  | ProcCall (_, _, p)
  | PredApp (_, _, p)
  | UnaryOp (_, _, p)
  | BinaryOp (_, _, _, _, p)
  | Ident (_, p) -> p
  | Annot (_, _, p) -> p  

let free_vars e =
  let rec fv bv acc = function
    | Ident (x, _) ->
        if IdSet.mem x bv then acc else IdSet.add x acc
    | Setenum (_, es, _)
    | New (_, es, _)
    | ProcCall (_, es, _)
    | PredApp (_, es, _) ->
        List.fold_left (fv bv) acc es
    | UnaryOp (_, e, _)
    | Old (e, _)
    | Length (e, _)
    | ArrayOfCell (e, _)
    | IndexOfCell (e, _)
    | ArrayCells (e, _)
    | Annot (e, _, _) ->
        fv bv acc e
    | Read (e1, e2, _) 
    | BinaryOp (e1, _, e2, _, _) ->
        fv bv (fv bv acc e1) e2
    | Binder (_, vs, e, _) ->
        let bv, acc =
          List.fold_left (fun (bv, acc) -> function
            | UnguardedVar v ->
                IdSet.add v.v_name bv, acc
            | GuardedVar (x, e) ->
                let acc = fv bv acc e in
                IdSet.add x bv, acc)
            (bv, acc) vs
        in
        fv bv acc e
    | _ -> acc
  in fv IdSet.empty IdSet.empty e
          
let pos_of_stmt = function
  | Skip pos
  | Block (_, pos)
  | LocalVars (_, _, pos)
  | Assume (_, _, pos)
  | Assert (_, _, pos)
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

let var_decl vname vtype vghost vimpl vpos vscope =
  { v_name = vname; v_type = vtype; v_ghost = vghost; v_implicit = vimpl; v_aux = false; v_pos = vpos; v_scope = vscope } 

let pred_decl hdr body =
  { hdr with pr_body = body }

let extend_spl_program incls decls bg_th prog =
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
      (prog.var_decls, prog.proc_decls, prog.pred_decls, prog.struct_decls)
      decls
  in
  { includes = incls @ prog.includes; 
    var_decls = vdecls; 
    struct_decls = sdecls; 
    proc_decls = pdecls;
    pred_decls = prdecls;
    background_theory = bg_th @ prog.background_theory;
  }

let merge_spl_programs prog1 prog2 =
  let vdecls =
    IdMap.fold (fun _ decl acc -> VarDecl decl :: acc) prog1.var_decls []
  in
  let sdecls =
    IdMap.fold (fun _ decl acc -> StructDecl decl :: acc) prog1.struct_decls vdecls
  in
  let prdecls =
    IdMap.fold (fun _ decl acc -> PredDecl decl :: acc) prog1.pred_decls sdecls
  in
  let decls =
    IdMap.fold (fun _ decl acc -> ProcDecl decl :: acc) prog1.proc_decls prdecls
  in
  extend_spl_program prog1.includes decls prog1.background_theory prog2

let add_alloc_decl prog =
  let alloc_decls =
    IdMap.fold
      (fun _ decl acc ->
        let sid = decl.s_name in
        let id = Prog.alloc_id (FreeSrt sid) in
        let tpe = SetType (StructType sid) in
        let pos = GrassUtil.dummy_position in
        let scope = GrassUtil.global_scope in
        let vdecl = VarDecl (var_decl id tpe true false pos scope) in
        vdecl :: acc
      )
      prog.struct_decls
      []
  in
    extend_spl_program [] alloc_decls [] prog

let empty_spl_program =
  { includes = [];
    var_decls = IdMap.empty;
    struct_decls = IdMap.empty;
    proc_decls = IdMap.empty;
    pred_decls = IdMap.empty;
    background_theory = [];
  }


let mk_block pos = function
  | [] -> Skip pos
  | [stmt] -> stmt
  | stmts -> Block (stmts, pos)

(** Pretty printing *)

open Format

let rec pr_type ppf = function
  | AnyRefType -> fprintf ppf "AnyRef" 
  | BoolType -> fprintf ppf "%s" bool_sort_string
  | IntType -> fprintf ppf "%s" int_sort_string
  | ByteType -> fprintf ppf "%s" byte_sort_string
  | UnitType -> fprintf ppf "Unit"
  | StructType id -> pr_ident ppf id
  | ArrayType e -> fprintf ppf "%s<@[%a@]>" array_sort_string pr_type e
  | ArrayCellType e -> fprintf ppf "%s<@[%a@]>" array_cell_sort_string pr_type e
  | MapType (d, r) -> fprintf ppf "%s<@[%a,@ %a@]>" map_sort_string pr_type d pr_type r
  | SetType s -> fprintf ppf "%s<@[%a@]>" set_sort_string pr_type s
  | PermType -> fprintf ppf "Permission"
  | AnyType -> fprintf ppf "Any"

let string_of_type t = pr_type str_formatter t; flush_str_formatter ()

