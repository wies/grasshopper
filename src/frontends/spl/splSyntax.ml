(** SPL abstract syntax. *)

open Grass

type idents = ident list

type pos = source_position

type name = string

type names = name list

(* this needs to be incorporated below *)
type qualified_ident = ident * ident

type typ =
  | IdentType of ident
  | StructType of ident
  | ADType of ident
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
    { modules: module_decls;
      includes: (name * pos) list;
    }

(* note: change naming, consistency *)
and module_decl = 
    { mod_name: ident;
      mod_pos: pos;
      type_decls: typedecls;
      var_decls: vars;
      proc_decls: procs;
      pred_decls: preds;
      fun_decls: fundecls;
      macro_decls: macros;
      background_theory: (expr * pos) list; 
    }

and module_decls = module_decl IdMap.t

(* keeping this for reference purposes for now *)
(*
type spl_program =
    { includes: (name * pos) list;
      type_decls: typedecls;
      var_decls: vars;
      proc_decls: procs;
      pred_decls: preds;
      fun_decls: fundecls;
      macro_decls: macros;
      background_theory: (expr * pos) list; 
    }
*)

and decl =
  | ModuleDecl of module_decl
  | TypeDecl of typedecl
  | VarDecl of var
  | ProcDecl of proc
  | PredDecl of pred
  | MacroDecl of macro

and decls = decl list

and proc =
    { p_name: ident;
      p_formals: idents;
      p_returns: idents;
      p_locals: vars;
      p_contracts: contracts;
      p_is_lemma: bool;
      p_body: stmt; 
      p_pos: pos;
    }

and procs = proc IdMap.t

and pred =
    { pr_name: ident;
      pr_formals: idents;
      pr_outputs: idents;
      pr_locals: vars;
      pr_contracts: contracts;
      pr_body: expr option; 
      pr_pos: pos;
    }

and preds = pred IdMap.t

and var =
    { v_name: ident;
      v_type: typ; 
      v_ghost: bool;
      v_implicit: bool;
      v_aux: bool;
      v_pos: pos;
      v_scope: pos;
    }

and vars = var IdMap.t

and typedecl =
    { t_name: ident;
      t_def: type_def;      
      t_pos: pos;
    }

and type_def =
  | FreeTypeDef
  | StructTypeDef of vars
  | ADTypeDef of constrs

and constrs = constr list
and constr =
    { c_name: ident;
      c_args: var list;
      c_pos: pos;
    }
        
and typedecls = typedecl IdMap.t

and fundecl =
    { f_name: ident;
      f_args: typ list;
      f_res: typ;
      f_is_destr: bool;
    }

and fundecls = fundecl IdMap.t

and macro =
    { m_name: ident;
      m_args: idents;
      m_body: expr;
      m_pos: pos;
    }

and macros = macro IdMap.t
      
and contract =
  | Requires of expr * bool * bool
  | Ensures of expr * bool * bool

and contracts = contract list

and stmt =
  | Skip of pos
  | Block of stmts * pos
  | LocalVars of var list * exprs option * pos
  | Assume of expr * bool * pos
  | Assert of expr * bool * pos
  | Split of expr * pos
  | Assign of exprs * exprs * pos
  | Havoc of exprs * pos
  | Dispose of expr * pos
  | If of expr * stmt * stmt * pos
  | Choice of stmts * pos
  | Loop of loop_contracts * stmt * expr * stmt * pos
  | Return of exprs * pos
  (* addition of Module and Open statements *)
  | Module of qualified_ident * pos
  | Open of qualified_ident * pos
  (* quotes to identify addition *)

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
  | Write of expr * expr * expr * pos
  | ConstrApp of ident * exprs * pos
  | DestrApp of ident * expr * pos
  | ProcCall of ident * exprs * pos
  | PredApp of pred_sym * exprs * pos
  | Binder of binder_kind * bound_var list * expr * pos
  | UnaryOp of un_op * expr * pos
  | BinaryOp of expr * bin_op * expr * typ * pos
  | Ident of ident * pos
  | Annot of expr * annotation * pos

and exprs = expr list

and bin_op = 
  | OpDiff | OpUn | OpInt 
  | OpMinus | OpPlus | OpMult | OpDiv | OpMod 
  | OpEq | OpGt | OpLt | OpGeq | OpLeq | OpIn
  | OpPts | OpSepStar | OpSepPlus | OpSepIncl
  | OpBvAnd | OpBvOr | OpBvShiftL | OpBvShiftR 
  | OpAnd | OpOr | OpImpl 

and un_op =
  | OpArrayCells | OpIndexOfCell | OpArrayOfCell | OpLength
  | OpUMinus | OpUPlus
  | OpBvNot | OpToInt | OpToByte
  | OpNot
  | OpOld
  | OpKnown
      
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
  | Write (_, _, _, p)
  | ConstrApp (_, _, p)
  | DestrApp (_, _, p)
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
    | ConstrApp (_, es, _)
    | PredApp (_, es, _) ->
        List.fold_left (fv bv) acc es
    | UnaryOp (_, e, _)
    | DestrApp (_, e, _)
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

(** Variable substitution for expressions (not capture avoiding) *)
let subst_id sm =
  let rec s bv = function
    | Ident (x, pos) as e ->
        if IdSet.mem x bv || not @@ IdMap.mem x sm
        then e
        else Ident (IdMap.find x sm, pos)
    | Setenum (ty, es, pos) ->
        Setenum (ty, List.map (s bv) es, pos)
    | New (ty, es, pos) ->
        New (ty, List.map (s bv) es, pos)
    | ProcCall (p, es, pos) ->
        ProcCall (p, List.map (s bv) es, pos)
    | PredApp (p, es, pos) ->
        PredApp (p, List.map (s bv) es, pos)
    | ConstrApp (c, es, pos) ->
        ConstrApp(c, List.map (s bv) es, pos)
    | DestrApp (d, e, pos) ->
        DestrApp (d, s bv e, pos)
    | UnaryOp (op, e, pos) ->
        UnaryOp (op, s bv e, pos)
    | Annot (e, a, pos) ->
        Annot (s bv e, a, pos) (* TODO: substitute in a *)
    | Read (e1, e2, pos) ->
        Read (s bv e1, s bv e2, pos)
    | BinaryOp (e1, op, e2, ty, pos) ->
        BinaryOp (s bv e1, op, s bv e2, ty, pos)
    | Binder (b, vs, e, pos) ->
        let bv =
          List.fold_left (fun bv -> function
            | UnguardedVar v ->
                IdSet.add v.v_name bv
            | GuardedVar (x, e) ->
                IdSet.add x bv)
            bv vs
        in
        Binder (b, vs, s bv e, pos)
    | e -> e
  in s IdSet.empty

(** General (id -> expr) substitution for expressions (not capture avoiding) *)
let subst sm =
  let rec s bv = function
    | Ident (x, pos) as e ->
        if IdSet.mem x bv || not @@ IdMap.mem x sm
        then e
        else IdMap.find x sm
    | Setenum (ty, es, pos) ->
        Setenum (ty, List.map (s bv) es, pos)
    | New (ty, es, pos) ->
        New (ty, List.map (s bv) es, pos)
    | ProcCall (p, es, pos) ->
        ProcCall (p, List.map (s bv) es, pos)
    | PredApp (p, es, pos) ->
        PredApp (p, List.map (s bv) es, pos)
    | ConstrApp (c, es, pos) ->
        ConstrApp(c, List.map (s bv) es, pos)
    | DestrApp (d, e, pos) ->
        DestrApp (d, s bv e, pos)
    | UnaryOp (op, e, pos) ->
        UnaryOp (op, s bv e, pos)
    | Annot (e, a, pos) ->
        Annot (s bv e, a, pos) (* TODO: substitute in a *)
    | Read (e1, e2, pos) ->  (* TODO Thomas, why no substitution for Write? *)
        Read (s bv e1, s bv e2, pos)
    | Write (e1, e2, e3, pos) ->
        Write (s bv e1, s bv e2, s bv e3, pos)
    | BinaryOp (e1, op, e2, ty, pos) ->
        BinaryOp (s bv e1, op, s bv e2, ty, pos)
    | Binder (b, vs, e, pos) ->
        let bv =
          List.fold_left (fun bv -> function
            | UnguardedVar v ->
                IdSet.add v.v_name bv
            | GuardedVar (x, e) ->
                IdSet.add x bv)
            bv vs
        in
        Binder (b, vs, s bv e, pos)
    | (Null _ | Emp _ | IntVal _ | BoolVal _) as e -> e
  in s IdSet.empty
    
let pos_of_stmt = function
  | Skip pos
  | Block (_, pos)
  | LocalVars (_, _, pos)
  | Assume (_, _, pos)
  | Assert (_, _, pos)
  | Split (_, pos)
  | Assign (_, _, pos)
  | Dispose (_, pos)
  | Havoc (_, pos)
  | If (_, _, _, pos)
  | Choice (_, pos)
  | Loop (_, _, _, _, pos)
  | Return (_, pos) -> pos
  (* addition of Module and Open here *)
  | Module (_, pos) -> pos
  | Open (_, pos) -> pos

let proc_decl hdr body =
  { hdr with p_body = body }

let struct_decl sname sfields pos =
  { t_name = sname;  t_def = StructTypeDef sfields; t_pos = pos }

let var_decl vname vtype vghost vimpl vpos vscope =
  { v_name = vname; v_type = vtype; v_ghost = vghost; v_implicit = vimpl; v_aux = false; v_pos = vpos; v_scope = vscope } 

let pred_decl hdr body =
  { hdr with pr_body = body }

(*
let module_decl mname mpos mbody = 
  { mbody with mod_name = mname; m_pos = mpos; }
*)

let extend_spl_program incls decls bg_th prog =
  let check_uniqueness id pos (tdecls, vdecls, pdecls, prdecls, mdecls) =
    if IdMap.mem id tdecls || IdMap.mem id vdecls || IdMap.mem id pdecls || IdMap.mem id prdecls
        || IdMap.mem id mdecls
    then ProgError.error pos ("redeclaration of identifier " ^ (fst id) ^ ".");
  in
  let module_decls, tdecls, vdecls, pdecls, prdecls, mdecls =
    List.fold_left (fun (module_decls, tdecls, vdecls, pdecls, prdecls, mdecls as decls) -> function
      | ModuleDecl delc ->
          check_uniqueness decl.mod_name decl.mod_pos decls;
          (* ??? *)
      | TypeDecl decl -> 
          check_uniqueness decl.t_name decl.t_pos decls;
          IdMap.add decl.t_name decl tdecls, vdecls, pdecls, prdecls, mdecls
      | VarDecl decl -> 
          check_uniqueness decl.v_name decl.v_pos decls;
          tdecls, IdMap.add decl.v_name decl vdecls, pdecls, prdecls, mdecls
      | ProcDecl decl -> 
          check_uniqueness decl.p_name decl.p_pos decls;
          tdecls, vdecls, IdMap.add decl.p_name decl pdecls, prdecls, mdecls
      | PredDecl decl -> 
          check_uniqueness decl.pr_name decl.pr_pos decls;
          tdecls, vdecls, pdecls, IdMap.add decl.pr_name decl prdecls, mdecls
      | MacroDecl decl ->
          check_uniqueness decl.m_name decl.m_pos decls;
          tdecls, vdecls, pdecls, prdecls, IdMap.add decl.m_name decl mdecls
      )
      (prog.type_decls, prog.var_decls, prog.proc_decls, prog.pred_decls, prog.macro_decls)
      decls
  in
  { includes = incls @ prog.includes;
    type_decls = tdecls;
    var_decls = vdecls; 
    proc_decls = pdecls;
    pred_decls = prdecls;
    fun_decls = IdMap.empty;
    macro_decls = mdecls;
    background_theory = bg_th @ prog.background_theory;
  }

let merge_spl_programs prog1 prog2 =
  let decls = []
    (* ??? *)
    |> IdMap.fold (fun _ decl acc -> ModuleDecl decl :: acc) prog1.module_decls
    |> IdMap.fold (fun _ decl acc -> TypeDecl decl :: acc) prog1.type_decls
    |> IdMap.fold (fun _ decl acc -> VarDecl decl :: acc) prog1.var_decls
    |> IdMap.fold (fun _ decl acc -> PredDecl decl :: acc) prog1.pred_decls
    |> IdMap.fold (fun _ decl acc -> ProcDecl decl :: acc) prog1.proc_decls
    |> IdMap.fold (fun _ decl acc -> MacroDecl decl :: acc) prog1.macro_decls
  in
  extend_spl_program prog1.includes decls prog1.background_theory prog2

let add_alloc_decl prog =
  let alloc_decls =
    IdMap.fold
      (fun _ decl acc ->
        match decl.t_def with
        | StructTypeDef _ ->
            let sid = decl.t_name in
            let id = Prog.alloc_id (FreeSrt sid) in
            let tpe = SetType (StructType sid) in
            let pos = GrassUtil.dummy_position in
            let scope = GrassUtil.global_scope in
            let vdecl = VarDecl (var_decl id tpe true false pos scope) in
            vdecl :: acc
        | _ -> acc)
      prog.type_decls
      []
  in
    extend_spl_program [] alloc_decls [] prog

let empty_spl_program =
  {
    modules = IdMap.empty;
    includes = [];
  }

(* keeping this here for reference purposes *)
(*
let empty_spl_program =
  { includes = [];
    type_decls = IdMap.empty;
    var_decls = IdMap.empty;
    proc_decls = IdMap.empty;
    pred_decls = IdMap.empty;
    fun_decls = IdMap.empty;
    macro_decls = IdMap.empty;
    background_theory = [];
  }
*)
    
let mk_block pos = function
  | [] -> Skip pos
  | [stmt] -> stmt
  | stmts -> Block (stmts, pos)

(** Replace all macro occurrences with macro body *)
let replace_macros prog =
  let rec repl_expr = function
    | ProcCall (p, es, pos) ->
      (match IdMap.find_opt p prog.macro_decls with
      | Some macro ->
        let sm =
          List.combine macro.m_args es
          |> List.fold_left (fun sm (v, e) -> IdMap.add v e sm) IdMap.empty
        in
        subst sm macro.m_body |> repl_expr
      | None ->
        ProcCall (p, List.map (repl_expr) es, pos))
    | (Null _ | Emp _ | IntVal _ | BoolVal _ | Ident _) as e -> e
    | Setenum (ty, es, pos) ->
      Setenum (ty, List.map (repl_expr) es, pos)
    | New (ty, es, pos) ->
      New (ty, List.map (repl_expr) es, pos)
    | Read (e1, e2, pos) ->
      Read (repl_expr e1, repl_expr e2, pos)
    | Write (e1, e2, e3, pos) ->
      Write (repl_expr e1, repl_expr e2, repl_expr e3, pos)
    | ConstrApp (c, es, pos) ->
      ConstrApp(c, List.map (repl_expr) es, pos)
    | DestrApp (d, e, pos) ->
      DestrApp (d, repl_expr e, pos)
    | PredApp (p, es, pos) ->
      PredApp (p, List.map (repl_expr) es, pos)
    | Binder (b, vs, e, pos) ->
      Binder (b, vs, repl_expr e, pos)
    | UnaryOp (op, e, pos) ->
      UnaryOp (op, repl_expr e, pos)
    | BinaryOp (e1, op, e2, ty, pos) ->
      BinaryOp (repl_expr e1, op, repl_expr e2, ty, pos)
    | Annot (e, a, pos) ->
      Annot (repl_expr e, a, pos)
  in
  let rec repl_stmt = function
    | Skip _ as s -> s
    | Block (sts, p) ->
      Block (List.map repl_stmt sts, p)
    | LocalVars (vs, es, p) ->
      LocalVars (vs, Util.Opt.map (List.map repl_expr) es, p)
    | Assume (e, b, p) ->
      Assume (repl_expr e, b, p)
    | Assert (e, b, p) ->
      Assert (repl_expr e, b, p)
    | Split (e, p) ->
      Split (repl_expr e, p)
    | Assign (vs, es, p) ->
      Assign (List.map repl_expr vs, List.map repl_expr es, p)
    | Dispose (e, p) ->
      Dispose (repl_expr e, p)
    | Havoc (es, p) ->
      Havoc (List.map repl_expr es, p)
    | If (e, st1, st2, p) ->
      If (repl_expr e, repl_stmt st1, repl_stmt st2, p)
    | Choice (stmts, p) ->
      Choice (List.map repl_stmt stmts, p)
    | Loop (invs, preb, cond, postb, p) ->
      let repl_loop_c = (function
        | Invariant (e, b) -> Invariant (repl_expr e, b))
      in
      Loop (List.map repl_loop_c invs, repl_stmt preb, repl_expr cond, repl_stmt postb, p)
    | Return (es, p) ->
      Return (List.map repl_expr es, p)
    | Module (qi, p) ->
      Module()
    | Open(qi, p) ->
      Open()
  in
  let repl_contr = function
    | Requires (e, b1, b2) -> Requires (repl_expr e, b1, b2)
    | Ensures (e, b1, b2) -> Ensures (repl_expr e, b1, b2)
  in
  let repl_proc proc =
    { proc with
      p_contracts = List.map repl_contr proc.p_contracts;
      p_body = repl_stmt proc.p_body;
    }
  in
  let repl_pred pred =
    { pred with
      pr_contracts = List.map repl_contr pred.pr_contracts;
      pr_body = Util.Opt.map repl_expr pred.pr_body;
    }
  in

  { prog with
    proc_decls = IdMap.map repl_proc prog.proc_decls;
    pred_decls = IdMap.map repl_pred prog.pred_decls;
  }


(** Pretty printing *)

open Format
 
let rec pr_type ppf = function
  | AnyRefType -> fprintf ppf "AnyRef" 
  | BoolType -> fprintf ppf "%s" bool_sort_string
  | IntType -> fprintf ppf "%s" int_sort_string
  | ByteType -> fprintf ppf "%s" byte_sort_string
  | UnitType -> fprintf ppf "Unit"
  | StructType id | IdentType id | ADType id -> pr_ident ppf id
  | ArrayType e -> fprintf ppf "%s<@[%a@]>" array_sort_string pr_type e
  | ArrayCellType e -> fprintf ppf "%s<@[%a@]>" array_cell_sort_string pr_type e
  | MapType (d, r) -> fprintf ppf "%s<@[%a,@ %a@]>" map_sort_string pr_type d pr_type r
  | SetType s -> fprintf ppf "%s<@[%a@]>" set_sort_string pr_type s
  | PermType -> fprintf ppf "Permission"
  | AnyType -> fprintf ppf "Any"

let pr_ghost ppf = function
  | true -> fprintf ppf "ghost "
  | false -> ()

let pr_implicit ppf = function
  | true -> fprintf ppf "implicit "
  | false -> ()

let pr_id_srt ppf (implicit, ghost, id, srt) =
  fprintf ppf "%a%a%a: %a" 
    pr_implicit implicit
    pr_ghost ghost
    pr_ident id 
    pr_type srt

let rec pr_id_srt_list ppf = function
  | [] -> ()
  | [v] -> pr_id_srt ppf v
  | v :: iss -> 
      fprintf ppf "%a,@ @,%a" 
        pr_id_srt v
        pr_id_srt_list iss

let pr_var ppf var =
  pr_id_srt ppf (var.v_implicit, var.v_ghost, var.v_name, var.v_type)

let pr_var_list = Util.pr_list_comma pr_var

let string_of_pred = function
  | AccessPred -> "acc"
  | BtwnPred -> "Btwn"
  | DisjointPred -> "Disjoint"
  | FramePred -> "Frame"
  | ReachPred -> "Reach"
  | Pred p -> string_of_ident p

let prio_of_expr = function
  | Null _ | Emp _ | IntVal _ | BoolVal _ | Ident _ -> 0
  | Read _ | Write _ | ProcCall _ | PredApp _ | ConstrApp _ | DestrApp _ | New _ | Setenum _ |
    Binder (SetComp, _, _, _) -> 1
  | UnaryOp ((OpArrayCells | OpIndexOfCell | OpArrayOfCell |
    OpLength | OpToInt | OpToByte | OpOld | OpKnown), _, _) -> 1
  | UnaryOp ((OpUMinus | OpUPlus | OpBvNot | OpNot), _, _) -> 2
  | BinaryOp (_, (OpMult | OpDiv | OpMod), _, _, _) -> 3
  | BinaryOp (_, (OpMinus | OpPlus), _, _, _) -> 4
  | BinaryOp (_, (OpBvShiftL | OpBvShiftR), _, _, _) -> 5
  | BinaryOp (_, (OpDiff | OpUn | OpInt), _, _, _) -> 6
  | BinaryOp (_, (OpGt | OpLt | OpGeq | OpLeq | OpIn | OpPts), _, _, _) -> 7
  | BinaryOp (_, OpEq, _, _, _) -> 8
  | BinaryOp (_, OpBvAnd, _, _, _) -> 9
  | BinaryOp (_, OpBvOr, _, _, _) -> 10
  | BinaryOp (_, OpAnd, _, _, _) -> 11
  | BinaryOp (_, OpSepStar, _, _, _) -> 12
  | BinaryOp (_, OpSepPlus, _, _, _) -> 13
  | BinaryOp (_, OpSepIncl, _, _, _) -> 14
  | BinaryOp (_, OpOr, _, _, _) -> 15
  | BinaryOp (_, OpImpl, _, _, _) -> 16
  | Binder _ -> 17
  | Annot _ -> 18

let is_left_assoc = function _ -> true
        
let rec pr_expr ppf =
  function
  | Ident (x, _) -> pr_ident ppf x
  | Null _ -> fprintf ppf "null"
  | Emp _ -> fprintf ppf "emp"
  | Setenum (ty, es, _) ->
      fprintf ppf "%s<%a>(@[%a@])"
        Grass.set_sort_string
        pr_type ty pr_expr_list es
  | IntVal (n, _) ->
      fprintf ppf "%s" (Int64.to_string n)
  | BoolVal (b, _) ->
      fprintf ppf "%b" b
  | New (ty, [], _) ->
      fprintf ppf "new %a" pr_type ty
  | New (ty, es, _) ->
      fprintf ppf "new %a(%a)" pr_type ty pr_expr_list es
  | Read (e1, e2, _) ->
      fprintf ppf "%a.%a" pr_expr e2 pr_expr e1
  | Write (e1, e2, e3, _) ->
      fprintf ppf "%a[%a := %a]" pr_expr e1 pr_expr e2 pr_expr e3
  | DestrApp (id, e, _) ->
      fprintf ppf "%a.%a" pr_expr e pr_ident id 
  | ConstrApp (id, es, _)
  | ProcCall (id, es, _) ->
      fprintf ppf "%a(@[%a@])" pr_ident id pr_expr_list es
  | PredApp (p, es, _) ->
      fprintf ppf "%s(@[%a@])" (string_of_pred p) pr_expr_list es
  | UnaryOp (op, e1, _) as e ->
      (match op with
      | OpArrayCells ->
          fprintf ppf "%a.cells" pr_expr e1
      | OpIndexOfCell ->
          fprintf ppf "%a.index" pr_expr e1
      | OpArrayOfCell ->
          fprintf ppf "%a.array" pr_expr e1
      | OpLength ->
          fprintf ppf "%a.length" pr_expr e1
      | OpUMinus | OpBvNot | OpUPlus | OpNot ->
          let op_str = match op with
          | OpUMinus -> "-"
          | OpUPlus -> "+"
          | OpBvNot -> "~"
          | OpNot -> "!"
          | _ -> ""
          in
          if prio_of_expr e < prio_of_expr e1
          then fprintf ppf "%s(@[%a@])" op_str pr_expr e1
          else fprintf ppf "%s%a" op_str pr_expr e1
      | OpOld ->
          fprintf ppf "old(@[%a@])" pr_expr e
      | OpKnown ->
          fprintf ppf "Known(@[%a@])" pr_expr e
      | OpToInt ->
          fprintf ppf "byte2int(@[%a@])" pr_expr e
      | OpToByte ->
          fprintf ppf "int2byte(@[%a@])" pr_expr e)
  | BinaryOp (e1, op, e2, _, _) as e ->
      let op_str = match op with
      | OpDiff -> "--"
      | OpUn -> "++"
      | OpInt -> "**"
      | OpMinus -> "-"
      | OpPlus -> "+"
      | OpMult -> "*"
      | OpDiv -> "/"
      | OpMod -> "%"
      | OpEq -> "=="
      | OpGt -> ">"
      | OpLt -> "<"
      | OpGeq -> ">="
      | OpLeq -> "<="
          (*(match ty with IntType -> "<=" | _ -> "subsetof")*)
      | OpIn -> "in"
      | OpPts -> "|->"
      | OpSepStar -> "&*&"
      | OpSepPlus -> "&+&"
      | OpSepIncl -> "-**"
      | OpBvAnd -> "&"
      | OpBvOr -> "|"
      | OpBvShiftL -> "<-<"
      | OpBvShiftR -> ">->"
      | OpAnd -> "&&"
      | OpOr -> "||"
      | OpImpl -> "==>"
      in
      let paran1, paran2 =
        if is_left_assoc op
        then
          (prio_of_expr e < prio_of_expr e1,
          prio_of_expr e <= prio_of_expr e2)
        else
          (prio_of_expr e < prio_of_expr e1,
          prio_of_expr e <= prio_of_expr e2)
      in
      let pr_paran paran ppf e =
        if paran
        then fprintf ppf "(%a)" pr_expr e
        else fprintf ppf "%a" pr_expr e
      in
      fprintf ppf "@[%a %s@ %a@]"
        (pr_paran paran1) e1
        op_str
        (pr_paran paran2) e2
        
  | Binder (b, vs, e, _) ->
      let pr_bound_var ppf = function
        | GuardedVar (x, e) ->
            fprintf ppf "%a@ in@ %a" pr_ident x pr_expr e
        | UnguardedVar v ->
            pr_var ppf v
      in
      (match b with
      | SetComp ->
          fprintf ppf "{ @[<2>%a ::@ %a@] }"
            (Util.pr_list_comma pr_bound_var) vs pr_expr e
      | _ ->
          let pr_binder = function
            | Forall -> "forall"
            | Exists -> "exists"
            | _ -> "???"
          in
          fprintf ppf "@[<2>%s %a ::@ %a@]"
            (pr_binder b) (Util.pr_list_comma pr_bound_var) vs pr_expr e
      )
  | Annot (e, _, _) -> pr_expr ppf e
and pr_expr_list es = Util.pr_list_comma pr_expr es
    
let pr_var_decl ppf (id, decl) =
  fprintf ppf "@[<2>var@ %a@];" 
    pr_id_srt (decl.v_implicit, decl.v_ghost, id, decl.v_type)

let pr_var_decls = Util.pr_list_nl pr_var_decl

let pr_adt_arg ppf (id, typ) =
  fprintf ppf "%a:@ %a" pr_ident id pr_type typ
    
let pr_adt_constr ppf cnst =
  fprintf ppf "%a(%a)" pr_ident cnst.c_name pr_var_list cnst.c_args
    
let rec pr_adt_constrs ppf = function
  | [] -> ()
  | [c] -> pr_adt_constr ppf c
  | c :: cs -> fprintf ppf "%a@ |@ %a" pr_adt_constr c pr_adt_constrs cs
    
let pr_type_decl ppf (_, tyd) =
  match tyd.t_def with
  | FreeTypeDef -> fprintf ppf "type@ @[%a@];@\n" pr_ident tyd.t_name
  | StructTypeDef sfields ->
      fprintf ppf "struct %a {@\n@[<2>  %a@]@\n}@\n"
        pr_ident tyd.t_name pr_var_decls (IdMap.bindings sfields)
  | ADTypeDef cnsts ->
      fprintf ppf "datatype %a = @[%a@];@\n" pr_ident tyd.t_name pr_adt_constrs cnsts
        
let pr_contract ppf = function
  | Requires (e, pure, free) ->
      fprintf ppf "@[<2>%s%srequires@ %a@]"
        (if pure then "pure " else "")
        (if free then "free " else "")
        pr_expr e
  | Ensures (e, pure, free) ->
      fprintf ppf "@[<2>%s%sensures@ %a@]"
        (if pure then "pure " else "")
        (if free then "free " else "")
        pr_expr e

let pr_contracts ppf cs =
  match cs with
  | [] -> ()
  | _ -> fprintf ppf "@\n%a" (Util.pr_list_nl pr_contract) cs

let pr_pred_decl ppf pred =
  let lookup = List.map (fun id -> IdMap.find id pred.pr_locals) in
  let pr_header ppf pred =
  match pred.pr_outputs with
  | [] ->
      fprintf ppf "@[<2>predicate %a(@[<0>%a@])%a@]@ "
        pr_ident pred.pr_name
        pr_var_list (lookup pred.pr_formals)
        pr_contracts pred.pr_contracts
  | _ ->
      fprintf ppf "@[<2>function %a(@[<0>%a@])@\nreturns (@[<0>%a@])%a@]@\n"
        pr_ident pred.pr_name
        pr_var_list (lookup pred.pr_formals)
        pr_var_list (lookup pred.pr_outputs)
        pr_contracts pred.pr_contracts
  in
  let pr_body ppf pred =
    match pred.pr_body with
    | Some sf ->
        fprintf ppf "{@[<1>@\n%a@]@\n}@\n" pr_expr sf
    | None -> fprintf ppf "@\n"
  in
  fprintf ppf "%a%a" pr_header pred pr_body pred
    
let rec pr_stmt ppf =
  let pr_invariant ppf =
    function Invariant (e, p) ->
      fprintf ppf "%sinvariant @[<2>%a@]"
        (if p then "pure " else "") pr_expr e
  in
  function
  | Skip _ -> fprintf ppf "{ }"
  | Block (sts, _) ->
      fprintf ppf "{@\n@[<2>  %a@]@\n}" pr_stmt_list sts
  | LocalVars (vs, None, _) ->
      fprintf ppf "var @[<2>%a];" pr_var_list vs
  | LocalVars (vs, Some es, _) ->
      fprintf ppf "var @[<2>%a :=@ %a@];" pr_var_list vs pr_expr_list es
  | Assume (e, p, _) ->
      fprintf ppf "%sassume @[<2>%a@];" (if p then "pure " else "") pr_expr e
  | Assert (e, p, _) ->
      fprintf ppf "%sassert @[<2>%a@];" (if p then "pure " else "") pr_expr e
  | Split (e, _) ->
      fprintf ppf "split @[<2>%a@]" pr_expr e
  | Assign ([], es, _) ->
      fprintf ppf "@[<2>%a@];" pr_expr_list es
  | Assign (vs, es, _) ->
      fprintf ppf "@[<2>%a :=@ %a@];" pr_expr_list vs pr_expr_list es
  | Dispose (e, _) ->
      fprintf ppf "free @[<2>%a@];" pr_expr e
  | Havoc (es, _) ->
      Util.pr_list_nl (fun ppf -> fprintf ppf "havoc %a;" pr_expr) ppf es
  | If (e, st1, Skip _, _) ->
      fprintf ppf "if (@[%a@]) %a"
        pr_expr e pr_stmt st1
  | If (e, st1, st2, _) ->
      fprintf ppf "if (@[%a@]) %a else %a"
        pr_expr e pr_stmt st1 pr_stmt st2
  | Choice (stmts, _) ->
      fprintf ppf "@<-3>%s@ %a" "choose" pr_choice stmts
  | Loop (invs, Skip _, cond, postb, _) ->
      fprintf ppf "while (@[%a@])@\n@[<2>  %a@]@\n%a"
        pr_expr cond (Util.pr_list_nl pr_invariant) invs pr_stmt postb
  | Loop (invs, preb, cond, postb, _) ->
      fprintf ppf "do %a while (@[%a@])@\n@[<2>  %a@]@\n%a"
        pr_stmt preb pr_expr cond
        (Util.pr_list_nl pr_invariant) invs
        pr_stmt postb
  | Return (es, _) ->
      fprintf ppf "return @[<2>%a@];" pr_expr_list es
and pr_stmt_list sts = Util.pr_list_nl pr_stmt sts 

and pr_choice ppf = function
  | [] -> ()
  | [stmt] -> pr_stmt ppf stmt
  | stmt :: stmts -> fprintf ppf "%a@ @<-3>%s@ %a" pr_stmt stmt "or" pr_choice stmts

    
let pr_proc_body locals ppf = function
  | Skip _ -> ()
  | st ->
      let sts = match st with
      | Block (sts, _) -> sts
      | _ -> [st]
      in
      fprintf ppf "{@[<1>@\n%a@\n%a@]@\n}"
        pr_var_decls locals
        (Util.pr_list_nl pr_stmt) sts 
    
let pr_proc_decl ppf proc =
  let lookup = List.map (fun id -> IdMap.find id proc.p_locals) in
  let locals = IdMap.fold (fun id decl locals ->
    if List.mem id (proc.p_returns @ proc.p_formals)
    then locals
    else (id, decl) :: locals) proc.p_locals []
  in
  let pr_returns ppf = function
    | [] -> ()
    | returns -> fprintf ppf "returns (@[<0>%a@])" pr_var_list (lookup returns)
  in
  fprintf ppf "@[<2>%s %a(@[<0>%a@])@\n%a%a@]@\n%a@\n"
    (if proc.p_is_lemma then "lemma" else "procedure")
    pr_ident proc.p_name
    pr_var_list (lookup proc.p_formals)
    pr_returns proc.p_returns
    pr_contracts proc.p_contracts
    (pr_proc_body locals) proc.p_body

let pr_fun_decl ppf fdecl =
  fprintf ppf "@[<2>%a(%a): %a;@]"
    pr_ident fdecl.f_name
    (Util.pr_list_comma pr_type) fdecl.f_args
    pr_type fdecl.f_res
    
let pr_axiom ppf (e, _) =
  fprintf ppf "@[<2>axiom@ %a@];@\n"
    pr_expr e 
    
let pr_cu ppf cu =
  let fld_ids =
    IdMap.fold (fun _ tdecl fld_ids ->
      match tdecl.t_def with
      | FreeTypeDef -> fld_ids
      | StructTypeDef fields ->
          IdMap.fold (fun id _ fld_ids -> IdSet.add id fld_ids) fields fld_ids
      | ADTypeDef _ -> fld_ids)
      cu.type_decls IdSet.empty
  in
  let globals =
    IdMap.filter
      (fun id _ -> not @@ IdSet.mem id fld_ids) cu.var_decls
  in
  fprintf ppf "%a@\n%a@\n%a@\n%a@\n%a"
    (Util.pr_list_nl pr_type_decl) (IdMap.bindings cu.type_decls)
    (Util.pr_list_nl pr_var_decl) (IdMap.bindings globals)
    (Util.pr_list_nl pr_axiom) cu.background_theory
    (Util.pr_list_nl pr_pred_decl) (List.map snd (IdMap.bindings cu.pred_decls))
    (Util.pr_list_nl pr_proc_decl) (List.map snd (IdMap.bindings cu.proc_decls))

    
let print_cu out_ch prog = Util.print_of_format pr_cu prog out_ch

        
let string_of_type t = Util.string_of_format pr_type t

