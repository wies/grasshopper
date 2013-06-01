open Form
open FormUtil
open Axioms
open Entails

(** Source position *)

type source_position = {
    sp_file : string;
    sp_start_line : int;
    sp_start_col : int;
    sp_end_line : int;
    sp_end_col : int;
  }

(** Specification formulas *)

type spec_form =
  | SL of Sl.form 
  | FOL of form 

(** Commands *)

(** Assignment, x_1,...,x_n := e_1,...,e_n *)
type assign_command = {
    assign_lhs : ident list; (** name of the assigned variables *)
    assign_rhs : term list; (** assigned values *)
  }

(** Havoc, havoc x_1, ..., x_n *)
type havoc_command = {
    havoc_args : ident list;
  } 

(** Allocation, x := new T *)
type new_command = {
    new_lhs : ident;
    new_sort : sort;
  }

(** Deallocation, free x *)
type dispose_command = {
    dispose_arg : term;
  }
     
type spec_kind =
  | Free | Checked | Frecked

(** Assume or assert of pure formula *)
type spec = {
    spec_form : spec_form;
    spec_form_negated : form option;
    spec_kind : spec_kind;
    spec_name : string;
    spec_msg : (ident -> source_position -> string) option;
    spec_pos : source_position;
  } 

(** Procedure call, x_1,..., x_n := p(e_1,...,e_m) *)
type call_command = {
    call_lhs : ident list; (** x_1,...,x_n *)
    call_name : ident; (** p *)
    call_args : term list; (** e_1,...,e_m *)
  } 

(** Return from procedure *)
and return_command = {
    return_args : term list;
  }

(** Basic commands *)
type basic_command =
  | Assign of assign_command
  | Havoc of havoc_command
  | New of new_command
  | Dispose of dispose_command
  | Assume of spec
  | Assert of spec
  | Call of call_command
  | Return of return_command

(** Program point *)
type program_point = {
    pp_pos : source_position; (** the source position of the program fragment *)
    pp_modifies : IdSet.t; (** the set of modified variables of the program fragment *)
    pp_accesses : IdSet.t; (** the set of accessed variables of the program fragment *)
  }

(** Loop *)
type loop_command = {
    loop_inv : spec list; (** the loop invariant *)
    loop_prebody : command; (** the command executed before each test of the loop condition *)
    loop_test : form; (** the loop condition *)
    loop_postbody : command; (** the actual loop body *)
  }

(** Compound commands *)
and command =
  | Loop of loop_command * program_point
  | Choice of command list * program_point
  | Seq of command list * program_point
  | Basic of basic_command * program_point

(** Variable declaration *)
type var_decl = {
    var_name : ident; (** variable name *)
    var_orig_name : string; (** original name *)
    var_sort : sort; (** variable type *)
    var_is_ghost : bool; (** whether the variable is ghost *)
    var_is_aux : bool; (** whether the variable is an auxiliary variable *)
    var_pos : source_position; (** position of declaration *)
  }

(** Procedure declaration *)
type proc_decl = {
    proc_name : ident; (** procedure name *)
    proc_formals : ident list;  (** formal parameter list *)
    proc_returns : ident list; (** return parameter list *)
    proc_locals : var_decl IdMap.t; (** all local variables *)
    proc_precond : spec list; (** precondition *)
    proc_postcond : spec list; (** postcondition *)
    proc_body : command option; (* procedure body *)
    proc_pos : source_position; (** position of declaration *)
  }

(** Predicate declaration *)
type pred_decl = {
    pred_name : ident; (** predicate name *)
    pred_formals : ident list; (** formal parameter list *)
    pred_locals : var_decl IdMap.t; (** local variables *)
    pred_body : Sl.form; (** predicate body *)
    pred_pos : source_position; (** position of declaration *)
  } 

(** Program *)
type program = {
    prog_axioms : spec list; (** background axioms *)
    prog_vars : var_decl IdMap.t; (** global variables *)
    prog_preds : pred_decl IdMap.t; (** predicates *)
    prog_procs : proc_decl IdMap.t; (** procedures *)
  } 

(** Auxiliary functions for programs and declarations *)

let dummy_position = 
  { sp_file = "";
    sp_start_line = 0;
    sp_start_col = 0;
    sp_end_line = 0;
    sp_end_col = 0 
  }

let empty_prog = 
  { prog_axioms = [];
    prog_vars = IdMap.empty;
    prog_preds = IdMap.empty;
    prog_procs = IdMap.empty 
  }
    
let dummy_proc name = 
  { proc_name = name;
    proc_formals = [];
    proc_returns = [];
    proc_locals = IdMap.empty;
    proc_precond = [];
    proc_postcond = [];
    proc_body = None;
    proc_pos = dummy_position;
  }

let declare_global prog var =
  { prog with prog_vars = IdMap.add var.var_name var prog.prog_vars }

let declare_pred prog pred =
  { prog with prog_preds = IdMap.add pred.pred_name pred prog.prog_preds }

let declare_proc prog proc =
  { prog with prog_procs = IdMap.add proc.proc_name proc prog.prog_procs }


let procs prog = IdMap.fold (fun _ proc procs -> proc :: procs) prog.prog_procs []

let find_proc prog name = IdMap.find name prog.prog_procs

let find_pred prog name = IdMap.find name prog.prog_preds

let find_global prog name = IdMap.find name prog.prog_vars

let find_var prog proc name =
  try IdMap.find name proc.proc_locals 
  with Not_found -> IdMap.find name prog.prog_vars

let mk_fresh_var_decl decl pos =
  let id = fresh_ident (name decl.var_name) in
  { decl with 
    var_name = id;
    var_orig_name = name id; 
    var_pos = pos;
  }

let fold_procs fn init prog =
  IdMap.fold (fun _ proc acc -> fn acc proc) prog.prog_procs init

let map_procs fn prog =
  { prog with prog_procs = IdMap.map fn prog.prog_procs }

let iter_procs fn prog =
  IdMap.iter (fun _ proc -> fn prog proc) prog.prog_procs

(** Auxiliary functions for specifications *)

let mk_spec_form f name msg pos =
  { spec_form = f;
    spec_form_negated = None;
    spec_kind = Frecked;
    spec_name = name;
    spec_msg = msg;
    spec_pos = pos;
  }

let mk_free_spec_form f name msg pos =
  { spec_form = f;
    spec_form_negated = None;
    spec_kind = Free;
    spec_name = name;
    spec_msg = msg;
    spec_pos = pos;
  } 

let mk_checked_spec_form f name msg pos =
  { spec_form = f;
    spec_form_negated = None;
    spec_kind = Checked;
    spec_name = name;
    spec_msg = msg;
    spec_pos = pos;
  } 

let fold_spec_form fol_fn sl_fn sf =
  match sf.spec_form with
  | FOL f -> fol_fn f
  | SL f -> sl_fn f

let is_checked_spec sf =
  match sf.spec_kind with
  | Free -> false
  | Checked | Frecked -> true

let is_free_spec sf =
  match sf.spec_kind with
  | Free | Frecked -> true
  | Checked -> false

let is_sl_spec sf =
  match sf.spec_form with
  | SL _ -> true
  | FOL _ -> false

let subst_id_spec sm sf =
  match sf.spec_form with
  | FOL f -> 
      { sf with 
        spec_form = FOL (subst_id sm f);
        spec_form_negated = Util.optmap (subst_id sm) sf.spec_form_negated            
      }
  | SL f -> 
      { sf with 
        spec_form = SL (SlUtil.subst_id sm f);
        spec_form_negated = Util.optmap (subst_id sm) sf.spec_form_negated 
      }
  
let subst_spec sm sf =
  match sf.spec_form with
  | FOL f -> 
      { sf with 
        spec_form = FOL (subst_consts sm f);
        spec_form_negated = Util.optmap (subst_consts sm) sf.spec_form_negated            
      }
  | SL _ -> failwith "elim_assign: found SL formula that should have been desugared."
  
      
let old_id = fresh_ident "old"
let old_prefix = "$old_"

let oldify (name, num) = (old_prefix ^ name, num)

let oldify_term vars t =
  let subst_map = 
    IdSet.fold (fun var subst_map ->
      IdMap.add var (oldify var) subst_map)
      vars IdMap.empty
  in subst_id_term subst_map t

let oldify_form vars f =
  let subst_map = 
    IdSet.fold (fun var subst_map ->
      IdMap.add var (oldify var) subst_map)
      vars IdMap.empty
  in subst_id subst_map f

let oldify_spec vars sf =
  let old_form =
    match sf.spec_form with
    | FOL f -> FOL (oldify_form vars f)
    | SL f -> SL f (* todo: oldification for SL formulas *)
  in 
  let old_form_negated = Util.optmap (oldify_form vars) sf.spec_form_negated in
  { sf with 
    spec_form = old_form;
    spec_form_negated = old_form_negated 
  }

let old_to_fun f =
  let rec o2f = function
    | App (FreeSym (name, num as id), [], srt) ->
        let old_name = Str.regexp (Str.quote old_prefix ^ "\\(.*\\)") in
        if Str.string_match old_name name 0 
        then
          let id1 = (Str.matched_group 1 name, num) in
          App (FreeSym old_id, [App (FreeSym id1, [], srt)], srt)
        else App (FreeSym id, [], srt)
    | App (sym, ts, srt) -> 
        App (sym, List.map o2f ts, srt)
    | t -> t
  in map_terms o2f f

let unoldify =
  let old_name = Str.regexp (Str.quote old_prefix ^ "\\(.*\\)") in
  fun (name, num) ->
    if Str.string_match old_name name 0 
    then (Str.matched_group 1 name, num)
    else (name, num)
    
let unoldify_term t = 
  map_id_term unoldify t

let unoldify_form f =
  map_id unoldify f

let unoldify_spec sf =
  let unold_form =
    match sf.spec_form with
    | FOL f -> FOL (unoldify_form f)
    | SL f -> SL f (* todo: unoldification for SL formulas *)
  in 
  let unold_form_negated = Util.optmap unoldify_form sf.spec_form_negated in
  { sf with 
    spec_form = unold_form;
    spec_form_negated = unold_form_negated 
  }


(** Auxiliary functions for program points *)

let merge_src_positions pos1 pos2 =
  let start_line, start_col =
    if pos1.sp_start_line < pos2.sp_start_line 
    then pos1.sp_start_line, pos1.sp_start_col
    else if pos2.sp_start_line < pos1.sp_start_line
    then pos2.sp_start_line, pos2.sp_start_col
    else if pos1.sp_start_col < pos2.sp_start_col
    then pos1.sp_start_line, pos1.sp_start_col
    else pos2.sp_start_line, pos2.sp_start_col
  in
  let end_line, end_col =
    if pos1.sp_end_line > pos2.sp_end_line 
    then pos1.sp_end_line, pos1.sp_end_col
    else if pos2.sp_end_line > pos1.sp_end_line
    then pos2.sp_end_line, pos2.sp_end_col
    else if pos1.sp_end_col > pos2.sp_end_col
    then pos1.sp_end_line, pos1.sp_end_col
    else pos2.sp_end_line, pos2.sp_end_col
  in
  { pos1 with
    sp_start_line = start_line;
    sp_start_col = start_col;
    sp_end_line = end_line;
    sp_end_col = end_col;
  }

let start_pos pos = 
  { pos with
    sp_end_line = pos.sp_start_line;
    sp_end_col = pos.sp_start_col;
  }

let end_pos pos = 
  { pos with
    sp_start_line = pos.sp_end_line;
    sp_start_col = pos.sp_end_col;
  }

let mk_ppoint pos = 
  { pp_pos = pos; 
    pp_modifies = IdSet.empty;
    pp_accesses = IdSet.empty;
  }

let update_ppoint pp = function
  | Loop (lc, _) -> Loop (lc, pp)
  | Choice (cs, _) -> Choice (cs, pp)
  | Seq (cs, _) -> Seq (cs, pp)
  | Basic (bc, _) -> Basic (bc, pp)

let prog_point = function
  | Loop (_, pp) | Choice (_, pp) | Seq (_, pp) | Basic (_, pp) -> pp

let source_pos c = (prog_point c).pp_pos


(** Auxiliary functions for commands *)

let modifies c = (prog_point c).pp_modifies

let modifies_proc prog proc = 
  match proc.proc_body with
  | Some cmd -> IdSet.filter (fun id -> IdMap.mem id prog.prog_vars) (modifies cmd)
  | None -> IdSet.empty

let modifies_basic_cmd = function
  | Assign ac -> id_set_of_list ac.assign_lhs
  | Havoc hc -> id_set_of_list hc.havoc_args
  | New nc -> IdSet.singleton nc.new_lhs
  | Dispose _ 
  | Assume _
  | Assert _
  | Return _ 
  | Call _ -> IdSet.empty

let accesses c = (prog_point c).pp_accesses

let accesses_spec_form_acc acc sf =
  IdSet.union acc 
    (match sf.spec_form with
    | FOL f -> free_consts f
    | SL f -> SlUtil.free_consts_sl f)

let accesses_spec_form sf = 
  accesses_spec_form_acc IdSet.empty sf

let accesses_proc prog proc = 
  let body_accs =
    match proc.proc_body with
    | Some cmd -> accesses cmd
    | None -> IdSet.empty
  in
  IdSet.filter 
    (fun id -> IdMap.mem id prog.prog_vars)
    (List.fold_left accesses_spec_form_acc body_accs
       (proc.proc_precond @ proc.proc_postcond))

let accesses_basic_cmd = function
  | Assign ac -> 
      let rhs_accesses = 
        List.fold_left free_consts_term_acc IdSet.empty ac.assign_rhs 
      in
      IdSet.union (id_set_of_list ac.assign_lhs) rhs_accesses
  | Havoc hc -> id_set_of_list hc.havoc_args
  | New nc -> IdSet.singleton nc.new_lhs
  | Dispose dc -> free_consts_term dc.dispose_arg
  | Assume sf
  | Assert sf -> accesses_spec_form sf
  | Return rc -> List.fold_left free_consts_term_acc IdSet.empty rc.return_args
  | Call cc -> 
      List.fold_left free_consts_term_acc IdSet.empty cc.call_args

(** Smart constructors for commands *)

let mk_basic_cmd bcmd pos =
  let pp = mk_ppoint pos in
  Basic (bcmd, 
         { pp with 
           pp_modifies = modifies_basic_cmd bcmd;
           pp_accesses = accesses_basic_cmd bcmd; 
         }
        )

let mk_assign_cmd lhs rhs pos = 
  let ac = { assign_lhs = lhs; assign_rhs = rhs } in
  mk_basic_cmd (Assign ac) pos

let mk_havoc_cmd args pos = 
  let hc = { havoc_args = args } in
  mk_basic_cmd (Havoc hc) pos

let mk_new_cmd lhs srt pos = 
  let nc = { new_lhs = lhs; new_sort = srt } in
  mk_basic_cmd (New nc) pos

let mk_dispose_cmd t pos =
  let dc = { dispose_arg = t } in
  mk_basic_cmd (Dispose dc) pos

let mk_assume_cmd sf pos =
  mk_basic_cmd (Assume sf) pos

let mk_assert_cmd sf pos =
  mk_basic_cmd (Assert sf) pos

let mk_return_cmd args pos = 
  let rc = { return_args = args } in
  mk_basic_cmd (Return rc) pos

let mk_call_cmd ?(prog=None) lhs name args pos =
  let cc = {call_lhs = lhs; call_name = name; call_args = args} in
  let accs = accesses_basic_cmd (Call cc) in
  let pp = mk_ppoint pos in
  match prog with
  | None -> Basic (Call cc, { pp with pp_accesses = accs }) 
  | Some prog -> 
      let proc = find_proc prog name in
      let mods = modifies_proc prog proc in
      let accs = IdSet.union (accesses_proc prog proc) accs in
      let pp1 = 
        { pp with 
          pp_modifies = mods;
          pp_accesses = accs;
        }
      in
      Basic (Call cc, pp1)

let mk_seq_cmd cmds pos =
  let cmds1, mods, accs = 
    List.fold_right (function
      | Seq (cs, _) -> fun (cmds1, mods, accs) -> 
          List.fold_right (fun c (cmds1, mods, accs) ->
            c :: cmds1, 
            IdSet.union (modifies c) mods, 
            IdSet.union (accesses c) accs)
            cs (cmds1, mods, accs)
      | c -> fun (cmds1, mods, accs) -> 
          c :: cmds1, 
          IdSet.union (modifies c) mods, 
          IdSet.union (accesses c) accs)
      cmds ([], IdSet.empty, IdSet.empty)
  in
  let pp = mk_ppoint pos in
  let pp1 = 
    { pp with
      pp_modifies = mods;
      pp_accesses = accs;
    } 
  in
  match cmds1 with
  | [cmd] -> cmd
  | _ -> Seq (cmds1, pp1)

let mk_choice_cmd cmds pos =
  let cmds1, mods, accs = 
    List.fold_right (function
      | Choice (cs, _) -> fun (cmds1, mods, accs) -> 
          List.fold_right (fun c (cmds1, mods, accs) ->
            c :: cmds1, 
            IdSet.union (modifies c) mods, 
            IdSet.union (accesses c) accs)
            cs (cmds1, mods, accs)
      | c -> fun (cmds1, mods, accs) -> 
          c :: cmds1, 
          IdSet.union (modifies c) mods, 
          IdSet.union (accesses c) accs)
      cmds ([], IdSet.empty, IdSet.empty)
  in
  let pp = mk_ppoint pos in
  let pp1 = 
    { pp with
      pp_modifies = mods;
      pp_accesses = accs;
    } 
  in
  match cmds1 with
  | [cmd] -> cmd
  | _ -> Choice (cmds, pp1)

let mk_loop_cmd inv preb cond postb pos =
  let loop = 
    { loop_inv = inv;
      loop_prebody = preb;
      loop_test = cond;
      loop_postbody = postb;
    } 
  in
  let pp = mk_ppoint pos in
  let mods = IdSet.union (modifies preb) (modifies postb) in
  let accs = 
    IdSet.union
      (IdSet.union (accesses preb) (accesses postb))
      (List.fold_left (accesses_spec_form_acc) (free_consts cond) inv)
  in
  let pp1 = 
    { pp with
      pp_modifies = mods;
      pp_accesses = accs;
    } 
  in
  Loop (loop, pp1)

let mk_ite cond cond_pos then_cmd else_cmd pos =
  let t_cond = mk_spec_form (FOL cond) "if then" None cond_pos in
  let e_cond = mk_spec_form (FOL (mk_not cond)) "if else" None cond_pos in
  let t_assume = mk_assume_cmd t_cond cond_pos in
  let e_assume = mk_assume_cmd e_cond cond_pos in
  let t_block = mk_seq_cmd [t_assume; then_cmd] (source_pos then_cmd) in
  let e_block = mk_seq_cmd [e_assume; else_cmd] (source_pos else_cmd) in
  mk_choice_cmd [t_block; e_block] pos

let rec fold_basic_cmds f acc = function
  | Loop (lc, pp) ->
      let lpre, acc = fold_basic_cmds f acc lc.loop_prebody in
      let lpost, acc = fold_basic_cmds f acc lc.loop_postbody in
      mk_loop_cmd lc.loop_inv lpre lc.loop_test lpost pp.pp_pos, acc
  | Choice (cs, pp) ->
      let cs1, acc = 
        List.fold_right (fun c (cs1, acc) ->
          let c1, acc = fold_basic_cmds f acc c in
          c1 :: cs1, acc)
          cs ([], acc)
      in
      mk_choice_cmd cs1 pp.pp_pos, acc
  | Seq (cs, pp) ->
      let cs1, acc =
        List.fold_right (fun c (cs1, acc) ->
          let c1, acc = fold_basic_cmds f acc c in
          c1 :: cs1, acc)
          cs ([], acc)
      in 
      mk_seq_cmd cs1 pp.pp_pos, acc
  | Basic (bc, pp) ->
      f (bc, pp) acc

let map_basic_cmds f c =
  let c1, _ = fold_basic_cmds (fun c _ -> f c, ()) () c in
  c1


(** Pretty printing *)

open Format

let string_of_src_pos pos =
  if pos.sp_end_line = pos.sp_start_line 
  then 
    Printf.sprintf "File \"%s\", line %d, characters %d-%d" 
      pos.sp_file pos.sp_start_line pos.sp_start_col pos.sp_end_col
  else 
    Printf.sprintf "File \"%s\", line %d, character %d - line %d, character %d" 
      pos.sp_file pos.sp_start_line pos.sp_start_col pos.sp_end_line pos.sp_end_col

let pr_spec_form ppf sf =
  match sf.spec_form with
  | SL f -> fprintf ppf "%s" (Sl.to_string f)
  | FOL f -> pr_form ppf (old_to_fun f)

let pr_basic_cmd ppf = function
  | Assign ac -> 
      fprintf ppf "@[<2>%a@ :=@ %a@]" 
        pr_ident_list ac.assign_lhs 
        pr_term_list ac.assign_rhs
  | Havoc hc -> 
      fprintf ppf "@[<2>havoc@ %a@]" pr_ident_list hc.havoc_args
  | New nc -> 
      fprintf ppf "@[<2>%a@ :=@ new@ %a@]" 
        pr_ident nc.new_lhs 
        pr_sort nc.new_sort
  | Dispose dc -> 
      fprintf ppf "@[<2>free@ %a@]" pr_term dc.dispose_arg
  | Assume sf ->
      fprintf ppf "/* %s */@\n@[<2>assume@ %a@]" 
        sf.spec_name
        pr_spec_form sf
  | Assert sf ->
      fprintf ppf "/* %s */@\n@[<2>assert@ %a@]" 
        sf.spec_name
        pr_spec_form sf
  | Return rc -> 
      fprintf ppf "@[<2>return@ %a@]" pr_term_list rc.return_args
  | Call cc -> 
      fprintf ppf "@[<2>%a@ :=@ @[call@ %a(@[%a@])@]@]" 
        pr_ident_list cc.call_lhs 
        pr_ident cc.call_name 
        pr_term_list cc.call_args

let rec pr_invs ppf = function
  | [] -> ()
  | [sf] -> fprintf ppf "invariant@ @[<2>%a@];" pr_spec_form sf
  | sf :: sfs -> fprintf ppf "@<0>%s@[<2>@ %a@];@\n%a" "invariant" pr_spec_form sf pr_invs sfs 

let rec pr_cmd ppf = function
  | Loop (lc, _) ->
      fprintf ppf "%awhile@ (%a)@ @,@[<2>@ @ %a@]@\n%a" 
        pr_cmd lc.loop_prebody 
        pr_form lc.loop_test 
        pr_invs lc.loop_inv 
        pr_cmd lc.loop_postbody
  | Choice (cs, _) ->
      fprintf ppf "@<-3>%s@ %a" "choose" pr_choice cs
  | Seq ([], _) -> ()
  | Seq (cs, _) ->
      fprintf ppf "{@[<1>@\n%a@]@\n}" pr_seq cs
  | Basic (bc, _) ->
      fprintf ppf "%a;" pr_basic_cmd bc

and pr_choice ppf = function
  | [] -> ()
  | [c] -> pr_cmd ppf c
  | c :: cs -> fprintf ppf "%a@ @<-3>%s@ %a" pr_cmd c "or" pr_choice cs

and pr_seq ppf = function
  | [] -> ()
  | [c] -> pr_cmd ppf c
  | c :: cs -> fprintf ppf "%a@\n%a" pr_cmd c pr_seq cs

let pr_spec_kind ppf = function
  | Free -> fprintf ppf "@<0>%s" "free "
  | Checked -> fprintf ppf "@<0>%s" "check "
  | Frecked -> ()

let rec pr_precond ppf = function
  | [] -> ()
  | sf :: sfs -> 
      fprintf ppf "/* %s */@\n@[<2>%arequires@ %a@];@\n%a"
        sf.spec_name
        pr_spec_kind sf.spec_kind
        pr_spec_form sf 
        pr_precond sfs 

let rec pr_postcond ppf = function
  | [] -> ()
  | sf :: sfs -> 
      fprintf ppf "/* %s */@\n@[<2>%aensures@ %a@];@\n%a"
        sf.spec_name
        pr_spec_kind sf.spec_kind
        pr_spec_form sf 
        pr_postcond sfs 

let pr_ghost ppf = function
  | true -> fprintf ppf "ghost "
  | false -> ()

let pr_id_srt ghost ppf (id, srt) =
  fprintf ppf "%a%a: %a" 
    pr_ghost ghost
    pr_ident id 
    pr_sort srt

let rec pr_id_srt_list ppf = function
  | [] -> ()
  | [ghost, is] -> pr_id_srt ghost ppf is
  | (ghost, is) :: iss -> 
      fprintf ppf "%a,@ @,%a" 
        (pr_id_srt ghost) is 
        pr_id_srt_list iss

let pr_body ppf = function
  | None -> ()
  | Some (Seq _ as c) -> pr_cmd ppf c 
  | Some c -> pr_cmd ppf (Seq ([c], mk_ppoint dummy_position))

let pr_var_decl ppf (id, decl) =
  fprintf ppf "%avar@ @[<2>%a@];@\n@\n" 
    pr_ghost decl.var_is_ghost
    (pr_id_srt false) (id, decl.var_sort)

let rec pr_var_decls ppf = function
  | [] -> ()
  | decl :: decls -> fprintf ppf "%a%a" pr_var_decl decl pr_var_decls decls

let pr_proc ppf proc =
  let add_srts = List.map (fun id -> 
    let decl = IdMap.find id proc.proc_locals in
    (decl.var_is_ghost, (id, decl.var_sort)))
  in
  let locals = IdMap.fold (fun id decl locals ->
    if List.mem id (proc.proc_returns @ proc.proc_formals) 
    then locals
    else (decl.var_is_ghost, (id, decl.var_sort)) :: locals) proc.proc_locals []
  in
  fprintf ppf "@[<2>procedure@ %a(@[<0>%a@])@]@ @,returns (@[<0>%a@])@ @,locals (@[<0>%a@])@\n%a%a%a@\n"
    pr_ident proc.proc_name
    pr_id_srt_list (add_srts proc.proc_formals)
    pr_id_srt_list (add_srts proc.proc_returns)
    pr_id_srt_list locals
    pr_precond proc.proc_precond
    pr_postcond proc.proc_postcond
    pr_body proc.proc_body

let rec pr_procs ppf = function
  | [] -> ()
  | proc :: procs ->
      fprintf ppf "%a@\n%a" pr_proc proc pr_procs procs

let pr_prog ppf prog =
  fprintf ppf "%a%a" 
    pr_var_decls (IdMap.bindings prog.prog_vars)
    pr_procs (List.map snd (IdMap.bindings prog.prog_procs))

let print_prog out_ch prog = fprintf (formatter_of_out_channel out_ch) "%a@?" pr_prog prog

let print_cmd out_ch cmd = fprintf (formatter_of_out_channel out_ch) "%a@?" pr_cmd cmd
