(** {5 Translation of SPL programs to internal representation } *)

open Util 
open Prog
open Sl
open Grass
open SplSyntax
open SplErrors
open SplChecker
open SplTypeChecker

(** Rewrite Boolean expressions to make the short-circuit evaluation semantics explicit.*)
let make_conditionals_lazy cu =
  let decl_aux_var name vtype pos scope locals =
    let aux_id = GrassUtil.fresh_ident name in
    let decl =
      { v_name = aux_id;
        v_type = vtype;
        v_ghost = false;
        v_implicit = false;
        v_aux = true;
        v_pos = pos;
        v_scope = scope;
      }
    in
    let locals1 = IdMap.add aux_id decl locals in
    aux_id, locals1
  in
  let rec process_stmt scope locals = function
    | If (BinaryOp(e1, OpOr, e2, _, p1), s1, s2, p2) -> If (e1, s1, If (e2, s1, s2, p1), p2), locals
    | Loop (invs, preb, BinaryOp (e1, OpOr, e2, _, pos1), postb, pos) ->
       let aux_id, locals = decl_aux_var "loop_cond" BoolType pos scope locals
       in
       Loop (Invariant (BinaryOp (Ident (aux_id, pos),
				  OpEq,
				  BinaryOp (e1, OpOr, e2, BoolType, pos1),
				  BoolType,
				  pos),
			true) :: invs,
	     Block (
		 [preb;
		  If (e1,
		      Assign ([Ident (aux_id, pos)], [BoolVal (true, pos)], pos),
		      If (e2,
			  Assign ([Ident (aux_id, pos)], [BoolVal (true, pos)], pos),
			  Assign ([Ident (aux_id, pos)], [BoolVal (false, pos)], pos),
			  pos),
		      pos)],
		 pos),
	     Ident (aux_id, pos1),
	     postb,
	     pos), locals
    | Block (ss, p) ->
       let ss, locals = List.fold_right
			  (fun s (s_list, locals) ->
			   let new_s, locals = process_stmt scope locals s
			   in
			   ([new_s] @ s_list), locals)
			  ss ([], locals)
       in
       Block (ss, p), locals
    | stmt -> stmt, locals
  in
  let procs =
    IdMap.fold
      (fun _ decl procs ->
        let body, locals = process_stmt decl.p_pos decl.p_locals decl.p_body in
        let decl1 = { decl with p_body = body; p_locals = locals } in
        IdMap.add decl.p_name decl1 procs)
      cu.proc_decls IdMap.empty
  in
  { cu with proc_decls = procs }


(** Convert compilation unit [cu] to abstract syntax of the intermediate language.
 *  Assumes that [cu] has been type-checked and flattened.
 *)
let convert cu =
  let find_var_decl pos locals id =
    try IdMap.find id locals 
    with Not_found -> 
      try IdMap.find id cu.var_decls
      with Not_found ->
        ProgError.error pos ("Unable to find identifier " ^ string_of_ident id)
  in
  let field_type pos fld_id locals =
    let fdecl = find_var_decl pos locals fld_id in
    fdecl.v_type
    (*with Not_found ->
      ProgError.error pos 
        ("Struct " ^ fst id ^ " does not have a field named " ^ fst fld_id)*)
  in
  let convert_type ty pos =
    let rec ct = function
      | StructType id -> Loc (FreeSrt id)
      | AnyRefType -> Loc (FreeSrt ("Null", 0))
      | MapType (dtyp, rtyp) -> Map (ct dtyp, ct rtyp)
      | SetType typ -> Set (ct typ)
      | ArrayType typ -> Loc (Array (ct typ))
      | ArrayCellType typ -> Loc (ArrayCell (ct typ))
      | IntType -> Int
      | ByteType -> Byte
      | BoolType -> Bool
      | ty -> failwith ("cannot convert type " ^ string_of_type ty ^ " near position " ^ string_of_src_pos pos)
    in
    ct ty
  in
  let convert_var_decl decl = 
    { var_name = decl.v_name;
      var_orig_name = fst decl.v_name;
      var_sort = convert_type decl.v_type decl.v_pos;
      var_is_ghost = decl.v_ghost;
      var_is_implicit = decl.v_implicit;
      var_is_aux = decl.v_aux;
      var_pos = decl.v_pos;
        var_scope = decl.v_scope;
    }
  in
  (** convert global variables *)
  let prog, globals =
    IdMap.fold
      (fun id decl (prog, globals) ->
        declare_global prog (convert_var_decl decl), IdSet.add decl.v_name globals)
      cu.var_decls (empty_prog, IdSet.empty)
  in
  let rec convert_term locals = function
    | Null (ty, pos) ->
        let cty = convert_type ty pos in
        let ssrt = GrassUtil.struct_sort_of_sort cty in
        GrassUtil.mk_null ssrt
    | Setenum (ty, es, pos) ->
        let ts = List.map (convert_term locals) es in
        let elem_ty =  convert_type ty pos in
        (match es with
        | [] -> GrassUtil.mk_empty (Set elem_ty)
        | _ -> GrassUtil.mk_setenum ts)
    | IntVal (i, _) ->
        GrassUtil.mk_int64 i
    | BoolVal (b, pos) ->
        App (BoolConst b, [], Bool)
    | Read (map, idx, pos) -> 
        let tmap = convert_term locals map in
        let tidx = convert_term locals idx in
        GrassUtil.mk_read tmap tidx
    | Old (e, pos) ->
        let t = convert_term locals e in
        oldify_term globals t
    | Length (e, pos) ->
        let t = convert_term locals e in
        GrassUtil.mk_length t
    | ArrayOfCell (e, pos) ->
        let t = convert_term locals e in
        GrassUtil.mk_array_of_cell t
    | IndexOfCell (e, pos) ->
        let t = convert_term locals e in
        GrassUtil.mk_index_of_cell t
    | ArrayCells (e, pos) ->
        let t = convert_term locals e in
        GrassUtil.mk_array_cells t
    | PredApp (Pred id, es, pos) ->
        let decl = IdMap.find id cu.pred_decls in
        let ts = List.map (convert_term locals) es in
        (match decl.pr_outputs with
        | [res] ->
            let res_decl = IdMap.find res decl.pr_locals in
            let res_srt = convert_type res_decl.v_type pos in
            GrassUtil.mk_free_fun res_srt id ts
        | [] ->
            let res_ty =
              decl.pr_body |>
              Opt.map (type_of_expr cu decl.pr_locals) |>
              Opt.get_or_else AnyType
            in
            let res_srt = convert_type res_ty pos in
            GrassUtil.mk_free_fun res_srt id ts
        | _ -> failwith "unexpected expression")
    | BinaryOp (e1, (OpDiff as op), e2, ty, _)
    | BinaryOp (e1, (OpUn as op), e2, ty, _)      
    | BinaryOp (e1, (OpInt as op), e2, ty, _) ->
        let mk_app =
          match op with
          | OpDiff -> GrassUtil.mk_diff
          | OpUn -> (fun t1 t2 -> GrassUtil.mk_union [t1; t2])
          | OpInt -> (fun t1 t2 -> GrassUtil.mk_inter [t1; t2])
          | _ -> failwith "unexpected operator"
        in
        let t1 = convert_term locals e1 in
        let t2 = convert_term locals e2 in
        mk_app t1 t2
    | BinaryOp (e1, (OpMinus as op), e2, ty, _)
    | BinaryOp (e1, (OpPlus as op), e2, ty, _)
    | BinaryOp (e1, (OpMult as op), e2, ty, _)
    | BinaryOp (e1, (OpDiv as op), e2, ty, _)
    | BinaryOp (e1, (OpBvAnd as op), e2, ty, _)
    | BinaryOp (e1, (OpBvOr as op), e2, ty, _)
    | BinaryOp (e1, (OpBvShiftL as op), e2, ty, _)
    | BinaryOp (e1, (OpBvShiftR as op), e2, ty, _) ->
        let mk_app =
          match op with
          | OpMinus -> GrassUtil.mk_minus
          | OpPlus -> GrassUtil.mk_plus
          | OpMult -> GrassUtil.mk_mult
          | OpDiv -> GrassUtil.mk_div
          | OpBvAnd -> GrassUtil.mk_bv_and
          | OpBvOr -> GrassUtil.mk_bv_or
          | OpBvShiftL -> GrassUtil.mk_bv_shift_left
          | OpBvShiftR -> GrassUtil.mk_bv_shift_right
          | _ -> failwith "unexpected operator"
        in
        let t1 = convert_term locals e1 in
        let t2 = convert_term locals e2 in
        mk_app t1 t2
    | UnaryOp (OpPlus, e, _) ->
        convert_term locals e
    | UnaryOp (OpMinus as op, e, _)
    | UnaryOp (OpBvNot as op, e, _)
    | UnaryOp (OpToInt as op, e, _)
    | UnaryOp (OpToByte as op, e, _) ->
        let t = convert_term locals e in
        let mk_app = match op with
          | OpMinus  -> GrassUtil.mk_uminus
          | OpBvNot  -> GrassUtil.mk_bv_not
          | OpToInt  -> GrassUtil.mk_byte_to_int
          | OpToByte -> GrassUtil.mk_int_to_byte
          | _ -> failwith "unexpected operator"
        in
        mk_app t
    | Ident (id, pos) ->
        let decl = find_var_decl pos locals id in
        let srt = convert_type decl.v_type pos in
        GrassUtil.mk_free_const srt decl.v_name
    | BinaryOp (e1, OpIn, e2, ty, pos) ->
        let t1 = convert_term locals e1 in
        let t2 = convert_term locals e2 in
        GrassUtil.mk_elem_term t1 t2
    | PredApp (FramePred, [set1; set2; fld1; fld2], pos) ->
        let tset1 = convert_term locals set1 in
        let tset2 = convert_term locals set2 in
        let tfld1 = convert_term locals fld1 in
        let tfld2 = convert_term locals fld2 in
        GrassUtil.mk_frame_term tset1 tset2 tfld1 tfld2
    | PredApp (DisjointPred, [set1; set2], pos) ->
        let tset1 = convert_term locals set1 in
        let tset2 = convert_term locals set2 in
        GrassUtil.mk_disjoint_term tset1 tset2
    | e -> failwith ("unexpected expression at " ^ string_of_src_pos (pos_of_expr e))
  in
  let rec convert_grass_form locals = function
    | BoolVal (b, pos) -> GrassUtil.mk_srcpos pos (GrassUtil.mk_bool b)
    | PredApp (BtwnPred, args, pos)
    | PredApp (ReachPred, args, pos) ->
        let fld, x, y, z =
          match args with
          | [fld; x; y; z] -> fld, x, y, z (* BtwnPred *)
          | [fld; x; y] -> fld, x, y, y (* ReachPred *)
          | _ -> failwith "impossible"
        in
        let tfld = convert_term locals fld in
        let tx = convert_term locals x in
        let ty = convert_term locals y in
        let tz = convert_term locals z in
        GrassUtil.mk_srcpos pos (GrassUtil.mk_btwn tfld tx ty tz)
    | Binder (q, decls, f, pos) ->
        let mk_guard = match q with
        | Forall -> GrassUtil.mk_implies
        | Exists -> fun f g -> GrassUtil.mk_and [f; g]
        | SetComp -> failwith "unexpected type"
        in
        let mk_quant vs f =
          let f0, ann = match f with
            | Grass.Binder (_, [], f0, ann) -> f0, ann
            | f0 -> f0, []
          in
          let f1 = match q with
            | Forall -> GrassUtil.mk_forall vs f0
            | Exists -> GrassUtil.mk_exists vs f0
            | SetComp -> failwith "unexpected type"
          in
          GrassUtil.annotate f1 ann
        in
        let (vars, (domains, locals1)) =
          Util.fold_left_map
            (fun (accD, accL) decl -> match decl with
              | GuardedVar (id, e) ->
                let e1 = convert_term accL e in
                (match type_of_expr cu accL e with
                | SetType elem_srt ->
                  let decl = var_decl id elem_srt false false pos pos in
                  let elem_srt = convert_type elem_srt pos in
                  let v_id = GrassUtil.mk_var elem_srt id in
                  (id, elem_srt), ((GrassUtil.mk_elem v_id e1) :: accD, IdMap.add id decl accL)
                | ty -> failwith "unexpected type after type inference" (*type_error (pos_of_expr e) (SetType AnyType) ty*))
              | UnguardedVar decl ->
                let id = decl.v_name in
                let ty = decl.v_type in
                (id, convert_type ty pos), (accD, IdMap.add id decl accL)
            )
            ([],locals)
            decls
        in
        let subst = 
          List.fold_right (fun (id, srt) subst -> 
            IdMap.add id (GrassUtil.mk_var srt id) subst)
            vars IdMap.empty
        in
        let f1 = convert_grass_form locals1 f in
        let f2 = mk_guard (GrassUtil.mk_and domains) f1 in
        let f3 = GrassUtil.subst_consts subst f2 in
        GrassUtil.mk_srcpos pos (mk_quant vars f3)
    | BinaryOp (e1, OpEq, e2, _, pos) ->
        (match type_of_expr cu locals e1 with
        | BoolType ->
            let f1 = convert_grass_form locals e1 in
            let f2 = convert_grass_form locals e2 in
            GrassUtil.mk_srcpos pos (GrassUtil.mk_iff f1 f2)
        | _ ->
            let t1 = convert_term locals e1 in
            let t2 = convert_term locals e2 in
            GrassUtil.mk_srcpos pos (GrassUtil.mk_eq t1 t2))
    | BinaryOp (e1, (OpGt as op), e2, ty, pos)
    | BinaryOp (e1, (OpLt as op), e2, ty, pos)
    | BinaryOp (e1, (OpGeq as op), e2, ty, pos)
    | BinaryOp (e1, (OpLeq as op), e2, ty, pos) ->
        let mk_int_form =
          match op with
          | OpGt -> GrassUtil.mk_gt
          | OpLt -> GrassUtil.mk_lt
          | OpGeq -> GrassUtil.mk_geq
          | OpLeq -> GrassUtil.mk_leq
          | _ -> failwith "unexpected operator"
        in
        let mk_set_form =
          match op with
          | OpGt -> (fun s t -> GrassUtil.mk_strict_subset t s)
          | OpLt -> GrassUtil.mk_strict_subset
          | OpGeq -> (fun s t -> GrassUtil.mk_subseteq t s)
          | OpLeq -> GrassUtil.mk_subseteq
          | _ -> failwith "unexpected operator"
        in
        let t1 = convert_term locals e1 in
        let t2 = convert_term locals e2 in
        (match type_of_expr cu locals e1 with
        | IntType | ByteType -> GrassUtil.mk_srcpos pos (mk_int_form t1 t2)
        | SetType _ -> GrassUtil.mk_srcpos pos (mk_set_form t1 t2)
        | ty -> failwith "unexpected type") 
    | UnaryOp (OpNot, e, pos) ->
        let f = convert_grass_form locals e in
        GrassUtil.mk_not f
    | BinaryOp (e1, (OpAnd as op), e2, _, _)
    | BinaryOp (e1, (OpOr as op), e2, _, _)
    | BinaryOp (e1, (OpImpl as op), e2, _, _) ->
        let f1 = convert_grass_form locals e1 in
        let f2 = convert_grass_form locals e2 in
        let mk_form = 
          match op with
          | OpAnd -> fun f1 f2 -> GrassUtil.smk_and [f1; f2]
          | OpOr -> fun f1 f2 -> GrassUtil.smk_or [f1; f2]
          | OpImpl -> GrassUtil.mk_implies           
          | _ -> failwith "unexpected operator"
        in
        mk_form f1 f2
    | Annot (e, CommentAnnot c, pos) ->
        let f = convert_grass_form locals e in
        GrassUtil.annotate f [Name (c, 0)]
    | Annot (e, PatternAnnot p, pos) ->
        let f = convert_grass_form locals e in
        let p1 = convert_term locals p in
        GrassUtil.mk_pattern p1 [] f
    | Annot (e, GeneratorAnnot (es, ge), pos) ->
        let f = convert_grass_form locals e in
        let es1 =
          List.map (fun (e, ids) ->
            let e1 = convert_term locals e in
            let filters = List.map (fun id -> FilterSymbolNotOccurs (FreeSym id)) ids in
            e1, filters)
            es
        in
        let ge1 = convert_term locals ge in
        let gts = GrassUtil.ground_terms (Atom (ge1, [])) in
        (*let filter id sm =
           
        in*)
        let matches = 
          List.map (fun (e, filters) -> 
            let ce = GrassUtil.free_consts_term e in
            let ce_occur_below ts =
              List.exists 
                (function App (FreeSym id, [], _) -> IdSet.mem id ce | _ -> false)
                ts
               in
            (*let rec ce_occur_below = function
              | App (FreeSym id, [], _) -> IdSet.mem id ce
              | App (_, ts, _) as t ->
                  t <> e && List.exists ce_occur_below ts
              | _ -> false
            in*)
            let flt = 
              TermSet.fold 
                (fun t acc -> match t with
                | App (FreeSym sym, (_ :: _ as ts), _)
                  when symbol_of e <> Some (FreeSym sym) && ce_occur_below ts ->
                    (FilterSymbolNotOccurs (FreeSym sym)) :: acc
                | App (Read, (App (FreeSym sym, [], srt) :: _ as ts), _)
                  when symbol_of e <> Some (FreeSym sym) && ce_occur_below ts ->
                    (FilterReadNotOccurs (GrassUtil.name sym, ([], srt))) :: acc
                | _ -> acc)
                gts (FilterNotNull :: filters)
            in
            Match (e, flt)) es1
        in
        GrassUtil.annotate f [TermGenerator (matches, [ge1])]
    | e ->
        let t = convert_term locals e in
        Grass.Atom (t, [SrcPos (pos_of_expr e)])
  in
  let rec convert_sl_form locals = function
    | Emp pos -> SlUtil.mk_emp (Some pos)
    | PredApp (AccessPred, [e], pos) ->
        let t = convert_term locals e in
        SlUtil.mk_region ~pos:pos t
    | PredApp (Pred id, es, pos) ->
        let ts = List.map (convert_term locals) es in 
        SlUtil.mk_pred ~pos:pos id ts
    | BinaryOp (e1, OpPts, e2, _, pos) ->
        let fld, ind = 
          match convert_term locals e1 with
          | App (Read, [fld; ind], _) -> fld, ind
          | _ -> 
              ProgError.error (pos_of_expr e1) 
                "Expected field access on left-hand-side of points-to predicate"
        in
        let t2 = convert_term locals e2 in
        SlUtil.mk_pts ~pos:pos fld ind t2
    | BinaryOp (e1, (OpSepStar as op), e2, _, pos)
    | BinaryOp (e1, (OpSepPlus as op), e2, _, pos)
    | BinaryOp (e1, (OpSepIncl as op), e2, _, pos) ->
        let mk_op = function
          | OpSepStar -> SlUtil.mk_sep_star
          | OpSepPlus -> SlUtil.mk_sep_plus
          | OpSepIncl -> SlUtil.mk_sep_incl
          | _ -> failwith "unexpected operator"
        in
        let f1 = convert_sl_form locals e1 in
        let f2 = convert_sl_form locals e2 in
        mk_op ~pos:pos op f1 f2
    | BinaryOp (e1, (OpAnd as op), e2, PermType, _)
    | BinaryOp (e1, (OpOr as op), e2, PermType, _) ->
        let f1 = convert_sl_form locals e1 in
        let f2 = convert_sl_form locals e2 in
        let mk_form = 
          match op with
          | OpAnd -> SlUtil.mk_and
          | OpOr -> SlUtil.mk_or
          | _ -> failwith "unexpected operator" 
        in
        mk_form f1 f2
    | Binder (Exists as q, decls, f, pos) ->
        let vars, locals1 = 
          List.fold_right (fun decl (vars, locals1) -> match decl with
            | UnguardedVar decl ->
              let id = decl.v_name in
              let ty = decl.v_type in
              (id, convert_type ty pos) :: vars, 
              IdMap.add id decl locals1
            | GuardedVar _ -> failwith "unexpected Guarded variable"
            )
            decls ([], locals)
        in
        let subst = 
          List.fold_right (fun (id, srt) subst -> 
            IdMap.add id (GrassUtil.mk_var srt id) subst)
            vars IdMap.empty
        in
        let mk_quant = match q with
        | Forall -> SlUtil.mk_forall 
        | Exists -> SlUtil.mk_exists
        | SetComp -> failwith "unexpected type"
        in
        let f1 = convert_sl_form locals1 f in
        let f2 = SlUtil.subst_consts subst f1 in
        mk_quant ~pos:pos vars f2
    | e ->
        let f = convert_grass_form locals e in
        Pure (f, Some (pos_of_expr e))
  in
  let convert_spec_form pure locals e name msg =
    let f = 
      if pure 
      then FOL (convert_grass_form locals e)
      else SL (convert_sl_form locals e)
    in
    mk_spec_form f name msg (pos_of_expr e)
  in
  let convert_loop_contract proc_name locals contract =
    List.map
      (function Invariant (e, pure) -> 
        let msg caller =
          if caller = proc_name then
            (Printf.sprintf 
               "An invariant might not hold before entering a loop in procedure %s"
               (string_of_ident proc_name),
             ProgError.mk_error_info "This is the loop invariant that might not hold initially")
          else 
            (Printf.sprintf 
               "An invariant might not be maintained by a loop in procedure %s"
               (string_of_ident proc_name),
             ProgError.mk_error_info "This is the loop invariant that might not be maintained")
        in
        (*let pos = pos_of_expr e in*)
        convert_spec_form pure locals e "invariant" (Some msg)
      )
      contract
  in
  let rec convert_stmt proc = 
    let convert_lhs es = 
      let ts = List.map (convert_term proc.p_locals) es in
      match ts with
      | [App (Read, [App (FreeSym fld, [], _); ind], _)] ->
          [fld], Some ind
      | _ -> 
          let ids = 
            List.map 
              (function 
                | Ident (id, _) -> id
                | e -> 
                    ProgError.error (pos_of_expr e) 
                      "Only variables are allowed on left-hand-side of simultaneous assignments"
              ) es                
          in
          ids, None
    in
    function
      | Skip pos -> mk_seq_cmd [] pos
      | Block (stmts, pos) ->
          let cmds = List.map (convert_stmt proc) stmts in
          mk_seq_cmd cmds pos
      | Assume (e, pure, pos) ->
          let sf = convert_spec_form pure proc.p_locals e "assume" None in
          mk_assume_cmd sf pos
      | Assert (e, pure, pos) ->
          let sf = convert_spec_form pure proc.p_locals e "assert" None in
          mk_assert_cmd sf pos
      | Assign (lhs, [ProcCall (id, es, cpos)], pos) ->
          let args = 
            List.map (convert_term proc.p_locals) es
          in 
          let lhs_ids, _ = convert_lhs lhs in
          mk_call_cmd lhs_ids id args cpos
      | Assign ([lhs], [New ((StructType _ as ty), es, npos)], pos)
      | Assign ([lhs], [New ((ArrayType _ as ty), es, npos)], pos) ->
          let lhs_ids, _ = convert_lhs [lhs] in
          let ts = List.map (convert_term proc.p_locals) es in
          let lhs_id = List.hd lhs_ids in
          mk_new_cmd lhs_id (convert_type ty npos) ts pos
      | Assign (lhs, rhs, pos) ->
          let rhs_ts = List.map (convert_term proc.p_locals) rhs in
          let lhs_ids, ind_opt = convert_lhs lhs in
          let cmd =
            (match ind_opt with
            | Some t ->
                let fld_id = List.hd lhs_ids in
                let fld_srt = convert_type (field_type pos fld_id proc.p_locals) pos in
                let fld = GrassUtil.mk_free_const fld_srt fld_id in
                mk_assign_cmd lhs_ids [GrassUtil.mk_write fld t (List.hd rhs_ts)] pos
            | None -> mk_assign_cmd lhs_ids rhs_ts pos)
          in
          cmd
      | Dispose (e, pos) ->
          let t = convert_term proc.p_locals e in
          mk_dispose_cmd t pos
      | Havoc (es, pos) ->
          let ids = 
            List.map
              (function 
                | Ident (id, _) -> id
                | e -> ProgError.error (pos_of_expr e) "Only variables can be havoced"
              )
              es
          in 
          mk_havoc_cmd ids pos
      | If (c, t, e, pos) ->
          let cond = convert_grass_form proc.p_locals c in
          let t_cmd = convert_stmt proc t in
          let e_cmd = convert_stmt proc e in
          let t_msg = "The 'then' branch of this conditional has been taken on the error trace" in
          let e_msg = "The 'else' branch of this conditional has been taken on the error trace" in
          mk_ite cond (pos_of_expr c) t_cmd e_cmd t_msg e_msg pos
      | Loop (contract, preb, cond, postb, pos) ->
          let preb_cmd = convert_stmt proc preb in
          let cond_pos = pos_of_expr cond in
          let cond = convert_grass_form proc.p_locals cond in
          let invs = convert_loop_contract proc.p_name proc.p_locals contract in
          let postb_cmd = convert_stmt proc postb in
          mk_loop_cmd invs preb_cmd cond cond_pos postb_cmd pos
      | Return (es, pos) ->
          let ts = List.map (convert_term proc.p_locals) es in
          mk_return_cmd ts pos
      | _ -> failwith "unexpected statement"
  in
  let prog =
    IdMap.fold 
      (fun id decl prog ->
        let rtype =
          decl.pr_body |>
          Opt.map (type_of_expr cu decl.pr_locals) |>
          Opt.get_or_else AnyType
        in
        let body, locals, outputs =
          match rtype with
          | BoolType ->
              let body = Opt.get_or_else (BoolVal (true, decl.pr_pos)) decl.pr_body in
              let cbody = convert_grass_form decl.pr_locals body in
              SL (Pure (cbody, Some (pos_of_expr body))), decl.pr_locals, decl.pr_outputs              
          | PermType ->
              let body = Opt.get_or_else (BoolVal (true, decl.pr_pos)) decl.pr_body in
              SL (convert_sl_form decl.pr_locals body), decl.pr_locals, decl.pr_outputs
          | rtype ->
              let ret_id, locals =
                match decl.pr_outputs with
                | [r] -> r, decl.pr_locals
                | _ ->
                    let res_id = GrassUtil.fresh_ident "res" in
                    let rdecl = 
                      { v_name = res_id;
                        v_type = rtype;
                        v_ghost = false;
                        v_implicit = false;
                        v_aux = true;
                        v_pos = decl.pr_pos;
                        v_scope = decl.pr_pos;
                      }
                    in
                    res_id, IdMap.add res_id rdecl decl.pr_locals
              in
              let r = Ident (ret_id, decl.pr_pos) in
              let body = match decl.pr_body with
              | Some (Binder (SetComp, vs, f, pos)) ->
                  let v_decl =
                    match vs with
                    | [UnguardedVar decl] -> decl
                    | _ -> failwith "unexpected set comprehension"
                  in
                  let v = Ident (v_decl.v_name, v_decl.v_pos) in
                  Binder (Forall, [UnguardedVar v_decl], BinaryOp (BinaryOp (v, OpIn, r, BoolType, pos), OpEq, f, BoolType, pos), pos)
              | Some e ->
                  BinaryOp (r, OpEq, e, BoolType, pos_of_expr e)
              | None -> BoolVal (true, decl.pr_pos)
              in
              FOL (convert_grass_form locals body), locals, [ret_id]
        in
        let locals = IdMap.map convert_var_decl locals in
        let body_pos =
          Opt.map pos_of_expr decl.pr_body |> Opt.get_or_else decl.pr_pos
        in
        let pred_decl = 
          { pred_name = id;
            pred_formals = decl.pr_formals;
            pred_outputs = outputs;
            pred_footprints = SortSet.empty;
            pred_locals = locals;
            pred_body = mk_spec_form body (string_of_ident id) None body_pos;
            pred_pos = decl.pr_pos;
            pred_accesses = IdSet.empty;
          }
        in
        declare_pred prog pred_decl
      )
      cu.pred_decls prog
  in
  let convert_contract proc_name locals contract =
    List.fold_right 
      (function 
        | Requires (e, pure) -> fun (pre, post) -> 
            let mk_msg caller =
              Printf.sprintf 
                "A precondition for this call of %s might not hold"
                (string_of_ident proc_name),
              ProgError.mk_error_info "This is the precondition that might not hold"
            in
            let name = "precondition of " ^ string_of_ident proc_name in
            convert_spec_form pure locals e name (Some mk_msg) :: pre, post
        | Ensures (e, pure) -> fun (pre, post) ->
            let mk_msg caller =
              Printf.sprintf 
                "A postcondition of procedure %s might not hold at this return point"
                (string_of_ident proc_name),
              ProgError.mk_error_info "This is the postcondition that might not hold"
            in 
            let name = "postcondition of " ^ string_of_ident proc_name in
            pre, convert_spec_form pure locals e name (Some mk_msg) :: post)
      contract ([], [])
  in
  let convert_body decl =
    match decl.p_body with
    | Skip _ -> None
    | _ -> Some (convert_stmt decl decl.p_body)
  in
  let prog =
    IdMap.fold
      (fun id decl prog ->
        let pre, post = convert_contract decl.p_name decl.p_locals decl.p_contracts in
        let proc_decl =
          { proc_name = id;
            proc_formals = decl.p_formals;
            proc_footprints = SortSet.empty;
            proc_returns = decl.p_returns;
            proc_locals = IdMap.map convert_var_decl decl.p_locals;
            proc_precond = pre;
            proc_postcond = post;
            proc_body = convert_body decl;
            proc_pos = decl.p_pos;
            proc_deps = [];
            proc_is_tailrec = false;
          } 
        in
        declare_proc prog proc_decl
      )
      cu.proc_decls prog
  in
  let prog = 
    let specs =
      List.map
        ( fun (e, pos) ->
          convert_spec_form true IdMap.empty e "axiom" None
        )
        cu.background_theory
    in
      { prog with prog_axioms = specs @ prog.prog_axioms }
  in
  prog

(** Convert compilation unit [cu] to abstract syntax of the intermediate language. *)
let to_program cu =
  let cu1 = make_conditionals_lazy cu in
  convert cu1
