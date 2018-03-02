open Util 
open Prog
open Sl
open Grass
open SplSyntax
open Debug


let removeGhost cu =

  (* collect the ghosts *)
  let keep_ghost map =
    let vars = IdMap.filter (fun _ v -> v.v_ghost) map in
    IdMap.fold (fun _ v acc -> IdSet.add v.v_name acc) vars IdSet.empty
  in
  let gs_global = keep_ghost cu.var_decls in
  let gs_procs = IdMap.map (fun p -> keep_ghost p.p_locals) cu.proc_decls in

  (* utils *)
  let is_ghost name id =
    let gproc = IdMap.find name gs_procs in
    IdSet.mem id gproc || IdSet.mem id gs_global
  in
  let is_implicit name id =
    try
      let proc = IdMap.find name cu.proc_decls in
      (*
      print_endline (string_of_ident name);
      print_endline "--------";
      List.iter (fun id -> print_endline (string_of_ident id)) proc.p_formals;
      print_endline "--------";
      List.iter (fun id -> print_endline (string_of_ident id)) proc.p_returns;
      print_endline "--------";
      IdMap.iter (fun id _ -> print_endline (string_of_ident id)) proc.p_locals;
      print_endline "========";
      *)
      let def = IdMap.find id proc.p_locals in
      def.v_implicit
    with _ -> failwith ("Not_found: is_implicit " ^ (string_of_ident name) ^ ", " ^ (string_of_ident id))
  in
  let rec has_stateful e = match e with
    | ProcCall _ | New _ -> true

    | Setenum (_, exprs, _) | PredApp (_, exprs, _) ->  List.exists has_stateful exprs

    | Read (expr1, expr2, _) | BinaryOp (expr1, _, expr2, _, _) -> List.exists has_stateful [expr1;expr2]

    | UnaryOp (_, expr, _) | Annot (expr, _, _) -> has_stateful expr

    | _ -> false
  in

  (* do the work *)
  let rec process_expr scope e = match e with
    | Null (t, p) -> Null (t, p)
    | Emp p -> Emp p
    | Setenum (t, exprs, p) -> Setenum (t, (List.map (process_expr scope) exprs), p)
    | IntVal (i, p) -> IntVal (i, p)
    | BoolVal (b, p) -> BoolVal (b, p)
    | New (t, exprs, p) -> New (t, (List.map (process_expr scope) exprs), p)
    | Read (fld, idx, p) -> Read ((process_expr scope fld), (process_expr scope idx), p) (*TODO ghost fields*)
    | Write (fld, idx, v, p) -> Write ((process_expr scope fld), (process_expr scope idx), (process_expr scope v), p) (*TODO ghost fields*)
    | ConstrApp (id, args, p) -> ConstrApp (id, List.map (process_expr scope) args, p)
    | DestrApp (id, e, p) -> DestrApp (id, process_expr scope e, p)
    | ProcCall (id, args, p) ->
      let formals = (IdMap.find id cu.proc_decls).p_formals in
      ProcCall (id, (process_args scope id formals args), p)
    | PredApp (ps, exprs, p) -> PredApp (ps, (List.map (process_expr scope) exprs), p)
    | UnaryOp (op, expr, p) -> UnaryOp (op, (process_expr scope expr), p)
    | BinaryOp (expr1, op, expr2, t, p) -> BinaryOp ((process_expr scope expr1), op, (process_expr scope expr2), t, p)
    | Binder (qkind, qvars, expr, p) -> Binder (qkind, qvars, (process_expr scope expr), p)
    | Ident (id, p) ->
      if is_ghost scope id then
        begin
          error (fun () -> "cannot erase: "^ (string_of_ident id) ^"\n");
          failwith ("cannot erase: "^ (string_of_ident id) ^"\n")
        end
      else
        Ident (id, p)
    | Annot (expr, annots, p) -> Annot ((process_expr scope expr), annots, p)
    | Dirty _ -> failwith "TODO - what should we do with dirty regions?"

  and process_args current_scope callee formals expr =
    let nonImplicit = List.filter (fun v -> not (is_implicit callee v)) formals in
    let paired = List.combine nonImplicit expr in
    let nonGhost =
      List.filter
        (fun (id, e) ->
          if is_ghost callee id then
            if has_stateful e then
              begin
                error (fun () -> "stateful operation about to get erased... not yet implemented\n");
                failwith "stateful operation about to get erased... not yet implemented\n"
              end
            else
              false
          else
            true
        )
        paired
        in
    List.map (fun (_, e) -> process_expr current_scope e) nonGhost
  in

  let rec process_stmt scope s = match s with
    | Skip p | Assume (_, _, p) | Assert (_, _, p) | Split (_, p) | Havoc (_, p) -> Skip p
    | Block (stmts, p) -> Block ((List.map (process_stmt scope) stmts), p)
    | Dispose (expr, p) -> Dispose ((process_expr scope expr), p)
    | If (cond, caseTrue, caseFalse, p) ->
      let cond2 = process_expr scope cond in
      let caseTrue2 = process_stmt scope caseTrue in
      let caseFalse2 = process_stmt scope caseFalse in
      If (cond2, caseTrue2, caseFalse2, p)
    | Choice (_, _) ->
        error (fun () -> "cannot compile nondeterministic choice statements\n");
        failwith "compiling nondeterministic choice"
    | Loop (contracts, pre, cond, body, p) ->
      let pre2 = process_stmt scope pre in
      let cond2 = process_expr scope cond in
      let body2 = process_stmt scope body in
      Loop ([], pre2, cond2, body2, p)
    | LocalVars (vars, exprs, p) ->
      warn (fun () -> "LocalVars statements should have been removed by name resolution phase.\n");
      LocalVars (vars, exprs, p)
    | Assign (lhs, [ProcCall (id, _, _) as pc], p) ->
      let pc2 = process_expr scope pc in
      let ret = (IdMap.find id cu.proc_decls).p_returns in
      let lhs2 = (process_args scope id ret lhs) in
      Assign (lhs2, [pc2], p)
    | Assign (lhs, rhs, p) ->
      let processed =
        List.fold_right2
          (fun l r acc ->
            match l with (*TODO ghost fields*)
            | Ident (id, p) ->
              if is_ghost scope id then
                if has_stateful r then
                  begin
                    error (fun () -> "stateful operation about to get erased... not yet implemented\n");
                    failwith "stateful operation about to get erased... not yet implemented\n"
                  end
                else
                  acc
              else
                (process_expr scope l, process_expr scope r) :: acc
            | l ->
              (process_expr scope l, process_expr scope r) :: acc
          )
          lhs rhs []
      in
      let lhs2, rhs2 = List.split processed in
      if (lhs2 = []) && (rhs2 = []) then Skip p
      else Assign (lhs2, rhs2, p)
    | Return (exprs, p) ->
      let ret = (IdMap.find scope cu.proc_decls).p_returns in
      Return ((process_args scope scope ret exprs), p)
  in

  let process_proc proc =
    { p_name = proc.p_name;
      p_formals = List.filter (fun v -> not (is_ghost proc.p_name v)) proc.p_formals;
      p_returns = List.filter (fun v -> not (is_ghost proc.p_name v)) proc.p_returns;
      p_locals = IdMap.filter (fun _ v -> not v.v_ghost) proc.p_locals;
      p_contracts = [];
      p_is_lemma = false;
      p_body = process_stmt proc.p_name proc.p_body;
      p_pos = proc.p_pos;
    }
  in

  let procs =
    IdMap.fold
      (fun id proc procs ->
        if proc.p_is_lemma then procs
        else IdMap.add id (process_proc proc) procs)
      cu.proc_decls IdMap.empty
  in
  
  let cu2 = 
    { includes = cu.includes;
      type_decls = cu.type_decls;
      var_decls = IdMap.filter (fun _ v -> not v.v_ghost) cu.var_decls;
      proc_decls = procs;
      pred_decls = IdMap.empty;
      fun_decls = IdMap.empty;
      macro_decls = IdMap.empty;
      background_theory = [];
    }
  in
  warn (fun () -> "ToDo remove ghost fields\n");
  cu2
