(** {5 Verification of GRASS programs} *)

open Util
open Grass
open GrassUtil
open Prog
open Simplifier
open Grassifier
    
(** Simplify the given program [prog] by applying all transformation steps. *)
let simplify procs prog =
  let dump_if n prog = 
    if !Config.dump_ghp == n 
    then (print_prog stdout prog; prog)
    else prog
  in
  let info msg prog = Debug.info (fun () -> msg); prog in
  prog |>
  dump_if 0 |>
  info "Encoding arrays.\n" |>
  elim_arrays |>
  info "Adding checks for run-time errors.\n" |>
  annotate_runtime_checks |>
  info "Eliminating new/free.\n" |>
  elim_new_dispose |>
  info "Inferring accesses.\n" |>
  Analyzer.infer_accesses false |>
  info "Pruning uncalled procedures and predicates.\n" |>
  Simplifier.prune_uncalled procs |>
  info "Eliminating loops.\n" |>
  elim_loops |>
  info "Eliminating dependencies on global state.\n" |>
  elim_global_deps |>
  dump_if 1 |>
  info "Eliminating SL specifications.\n" |>
  elim_sl |>
  Analyzer.infer_accesses false |>
  info "Eliminating unused formal parameters.\n" |>
  elim_unused_formals |>
  info "Adding frame axioms.\n" |>
  add_frame_axioms |>
  (*(fun prog -> if !Config.abstract_preds then annotate_frame_axioms prog else prog) |> *)
  (*annotate_term_generators |>*)
  dump_if 2 |>
  info "Eliminating return statements.\n" |>
  elim_return |>
  info "Transforming to SSA.\n" |>
  elim_state |>
  dump_if 3

(** Annotate [msg] as comment to leaves of formula [f] *)
let annotate_aux_msg msg f = 
  let annotate annot = 
    if List.exists (function ErrorMsg _ -> true | _ -> false) annot 
    then annot
    else 
      Util.partial_map 
        (function SrcPos pos -> Some (ErrorMsg (pos, msg)) | _ -> None)
        annot @ annot
  in
  let rec annotate_form = function
    | Binder (Forall as b, vs, (BoolOp (Or, fs) as f), annot)
    | Binder (Exists as b, vs, (BoolOp (And, fs) as f), annot) ->
        if List.for_all (function Atom (_, _) | BoolOp (Not, [Atom (_, _)]) -> true | _ -> false) fs &&
          List.exists (function SrcPos _ -> true | _ -> false) annot
        then Binder (b, vs, f, annotate annot)
        else 
          Binder (b, vs, annotate_form f, annotate annot)
    | Binder (b, vs, f, annot) ->
        Binder (b, vs, annotate_form f, annotate annot)
    | BoolOp (op, fs) -> 
        BoolOp (op, List.map annotate_form fs)
    | Atom (t, annot) -> Atom (t, annotate annot)
  in annotate_form f  

(** Add labels for trace generation and debugging to verification condition [vc] *)
let add_labels vc =
  let process_annot (ltop, annots) = function
    | ErrorMsg (pos, msg) ->
        let lbl = fresh_ident "Label" in
        IdMap.add lbl (pos, msg) ltop, 
        Label (true, mk_free_const Bool lbl) :: annots
    | ann -> ltop, ann :: annots
  in
  let rec al f ltop = 
    match f with
    | BoolOp (op, fs) -> 
        let ltop1, fs1 = 
          List.fold_right (fun f (ltop, fs1) -> 
            let ltop1, f1 = al f ltop in
            ltop1, f1 :: fs1) fs (ltop, [])
        in
        ltop1, BoolOp (op, fs1)
    | Binder (b, vs, f, annots) ->
        let ltop1, f1 = al f ltop in
        let ltop2, annots1 = List.fold_left process_annot (ltop1, []) annots in
        ltop2, Binder (b, vs, f1, annots1)
    | Atom (t, annots) -> 
        let ltop1, annots1 = List.fold_left process_annot (ltop, []) annots in
        ltop1, Atom (t, annots1)
  in
  al vc IdMap.empty


let add_match_filters =
  let add_filters = function
    (*| TermGenerator (_, [App (Known, _, _)]) as a -> a*)
    | TermGenerator (ms, (_ :: _ as ge)) ->
        let gts =
          ge |>
          List.fold_left subterms_term_acc TermSet.empty |>
          TermSet.filter (function App (_, _, Bool) | App (Known, _, _) -> false | _ -> true)
        in
        let process_match (e, filters) matches =
          let sym_of_e = match e with
          | App (Known, [e], _) -> symbol_of e
          | _ -> symbol_of e
          in
          let var_terms_of_e = sorted_fv_term_acc IdMap.empty e in
          let occurs_below_var_terms_of_e ts =
            List.exists 
              (function Var (id, _) -> IdMap.mem id var_terms_of_e | _ -> false)
              ts
          in
          let add f fs = if List.mem f fs then fs else f :: fs in
          let flt, aux_matches = 
            TermSet.fold 
              (fun t (flt, aux_matches) -> match t with
              | App ((ArrayOfCell | IndexOfCell | FreeSym _ | Constructor _ as sym), (_ :: _ as ts), srt)
                when sym_of_e <> Some sym && occurs_below_var_terms_of_e ts ->
                  add (FilterSymbolNotOccurs sym) flt, aux_matches
              | App (Read, ([App (FreeSym sym, [], srt); l] as ts), _)
                when sym_of_e <> Some (FreeSym sym) && occurs_below_var_terms_of_e ts ->
                  add (FilterReadNotOccurs (GrassUtil.name sym, ([], srt))) flt,
                  Match (l, [FilterNotNull]) :: aux_matches
              | _ -> flt, aux_matches)
              gts (filters, [])
          in
          (** add `known` guards for variables and yield terms of certain sorts *)
          let aux_matches =
            let g = List.hd (List.rev ge) in
            match sort_of g with
            | Int | Loc _ | FreeSrt _ | Set _ ->
                IdMap.fold
                  (fun id srt aux_matches ->
                    match srt with
                    | Int | FreeSrt _ | Loc _ as rsrt ->
                        Match (GrassUtil.mk_known (GrassUtil.mk_var rsrt id), []) :: aux_matches
                    | _ -> aux_matches
                  )
                  var_terms_of_e aux_matches
            | _ -> aux_matches
          in
          Match (e, flt) :: aux_matches @ matches
        in
        let matches = 
          List.fold_right (function Match (e, filters) -> process_match (e, filters)) ms []
        in
        (** make sure that all free variables in the yield term ge are matched by some match clause *)
        let extra_guards =
          let fv_ge = List.fold_left sorted_fv_term_acc IdMap.empty ge in
          let fv_matches =
            List.fold_left
              (fun acc -> function Match (e, _) -> sorted_fv_term_acc acc e)
              IdMap.empty matches
          in
          IdMap.fold (fun id srt extra_guards ->
            if IdMap.mem id fv_matches then extra_guards
            else Match (GrassUtil.mk_known (GrassUtil.mk_var srt id), []) :: extra_guards)
            fv_ge []
        in
        TermGenerator (matches @ extra_guards, ge)
  | a -> a
  in
  let rec pf = function
    | BoolOp (op, fs) -> BoolOp (op, List.map pf fs)
    | Binder (b, vs, f, a) -> Binder (b, vs, pf f, List.map add_filters a)
    | Atom (t, a) -> Atom (t, List.map add_filters a)
  in pf

(** Create term generators for formula [f]. If [f] is the definition of a predicate, 
  * then aux_match is is [Some (pid, m)] where [pid] is the name of the predicate and
  * and [m] is the associated matching trigger.
 *)
let add_generators prog aux_match f =
  (* if f defines a predicate, collect parameter variables of that predicate *)
  let aux_vs =
    Opt.fold (fun aux_vs -> function (pid, Match (t, _)) -> fv_term_acc aux_vs t)
      IdSet.empty aux_match
  in
  (* collect all function terms in [f] that contain quantified variables and for which we want term generators *)
  let fun_terms bvs f =
    let rec ft acc = function
      | App (sym, (_ :: _ as ts), srt) as t
        when (sym <> Read || IdSet.subset (fv_term t) aux_vs) &&
          (is_free_symbol sym || sym = Disjoint || sym = SubsetEq || srt <> Bool) ->
            let fvs = fv_term t in
            let sts = List.fold_left subterms_term_acc TermSet.empty ts in
            let no_var_reads =
              TermSet.for_all (function
                | App (Read, _ :: _ :: (Var (x, _) | App ((Plus | Minus), [Var (x, _); _], _)) :: _, _) -> IdSet.mem x aux_vs
                | App (Read, _ :: (Var (x, _) | App ((Plus | Minus), [Var (x, _); _], _)) :: _, _) -> IdSet.mem x aux_vs
                | _ -> true) sts
            in
            let expand =
              match sym with
              | FreeSym ("lt", _) -> false
              | FreeSym id ->
                  IdMap.find_opt id prog.prog_preds |>
                  Opt.map (fun pred ->
                    (match pred.pred_contract.contr_returns with
                    | id :: _ -> (IdMap.find id pred.pred_contract.contr_locals).var_sort <> Bool
                    | _ -> false) || 
                      pred.pred_body <> None) |>
                      Opt.get_or_else true
                    | _ -> true
            in
            (*if expand then print_endline ("Expand: " ^ string_of_symbol sym)
              else print_endline ("Not Expand: " ^ string_of_symbol sym);*)
            if (no_var_reads || is_set_sort srt) && IdSet.subset fvs bvs && not @@ IdSet.is_empty fvs
            then
              let acc1 = if expand then TermSet.add t acc else acc in
              List.fold_left ft acc1 ts
            else acc
      | App (sym, [], Adt _) as t ->
          TermSet.add t acc
      | App (_, ts, Bool) ->
          List.fold_left ft acc ts
      | App (t, ts, _) ->
          List.fold_left ft acc ts
      | _ -> acc              
    in
    fold_terms ft TermSet.empty f
  in
  (* create term generators for the relevant function terms *)
  let rec ag bvs = function
    | BoolOp (op, fs) ->
        BoolOp (op, List.map (ag bvs) fs)
    | Binder (Forall, vs, f, ann) ->
        let bvs = List.fold_left (fun bvs (v, _) -> IdSet.add v bvs) bvs vs in
        let aux_info =
          aux_match |>
          Opt.map (function (pid, Match (pt, _)) ->
            let pdecl = Prog.find_pred prog pid in
            let ppos =
              pdecl.pred_body |>
              Opt.map (fun s -> s.spec_pos) |>
              Opt.get_or_else dummy_position
            in
            pid, pt, ppos, pdecl)                         
        in
        let mk_read_vars srts =
          List.map (fun srt -> mk_var srt (fresh_ident "?i")) srts
        in
        let rec read_gens seen_adts gens t pt =
          match sort_of t, sort_of pt with
          | (Map _ | Adt _) as tsrt, Adt (tid, adts)
            when not @@ IdSet.mem tid seen_adts ->
              let cstrs =
                List.assoc tid adts in
              let destrs = flat_map (fun (_, destrs) -> destrs) cstrs in
              let seen_adts1 = IdSet.add tid seen_adts in
              List.fold_left
                (fun gens (destr, srt) ->
                  let srt = unfold_adts adts srt in
                  let read_pt = mk_destr srt destr pt in
                  let gens1, read_t = match tsrt with
                  | Adt (tid1, _) when tid = tid1 ->
                      let read_t = mk_destr srt destr t in
                      (read_pt, read_t) :: gens, read_t
                  | _ -> gens, t
                  in
                  read_gens seen_adts1 gens1 read_t read_pt
                )            
                gens destrs
          | (Map _ | Adt _) as tsrt, Map (dsrts, rsrt) ->
              let read_vars = mk_read_vars dsrts in
              let read_pt = mk_read pt read_vars in
              let gens1, read_t = match tsrt with
              | Map (tdsrts, trsrt)
                when tdsrts = dsrts && trsrt = rsrt ->
                  let read_t = mk_read t read_vars in
                  (read_pt, read_t) :: gens, read_t
              | _ -> gens, t
              in
              read_gens seen_adts gens1 read_t read_pt
          | _, Pat ->
              (match pt with
              | App (_, [pt], _) -> read_gens seen_adts gens t pt
              | _ -> gens)
          | srt1, srt2 when srt1 = srt2 -> (pt, t) :: gens
          | _ -> gens
        in
        let ft, read_gens =
          f |>
          fun_terms bvs |>
          TermSet.elements |>
          (*(fun ts -> List.iter (print_term_endline stdout) ts; ts) |>*)
          List.map (function
            | App (Disjoint, [t1; t2], _) -> mk_inter [t1; t2], []
            | App (SubsetEq, [t1; t2], _) -> mk_union [t1; t2], []
            | (App (Read, App (FreeSym id, _ :: _, _) :: _, srt)
            | App (Read, App (Read, Var (id, _) :: _, _) :: _, srt)
            | App (FreeSym id, _, srt)) as t -> begin
                aux_info |>
                Opt.map (fun (pid, pt, ppos, pdecl) ->
                  (*Printf.printf "read_gens %s %s\n" (string_of_term pt) (string_of_term t);*)
                  let read_gens =
                    read_gens IdSet.empty [] t pt |>
                    List.filter (fun (pt, t) -> pt <> t)
                  in                      
                  (* Add generator for propagating known terms to force unfolding of predicate definitions *)
                  (* Only do this if id is a predicate that is not the entry point into an SCC in the predicate call graph *)
                  let dont_make_known =
                    IdMap.find_opt id prog.prog_preds |>
                    Opt.map (fun decl ->
                      pdecl.pred_contract.contr_name = decl.pred_contract.contr_name ||
                      IdSet.mem pid (accesses_pred decl) &&
                      not (contained_in_src_pos decl.pred_contract.contr_pos ppos)) |>
                      Opt.get_or_else true
                  in
                  if dont_make_known
                  then (t, read_gens)
                  else (mk_known t, read_gens)) |>
                  Opt.get_or_else (t, [])                    
            end
            | t -> t, []) |>
              List.split         
        in
        let read_gens =
          List.flatten read_gens |>
          List.map (fun (read_pt, read_t) ->
            let ms =
              IdMap.fold (fun id srt ms -> Match (mk_var srt id, []) :: ms)
                (sorted_fv_term_acc IdMap.empty read_t)
                []
            in
            TermGenerator (Match (read_pt, []) :: ms, [read_t]))
        in
        let ms =
          IdMap.fold (fun id srt ms -> Match (mk_var srt id, []) :: ms)
            (List.fold_left sorted_fv_term_acc IdMap.empty ft)
            []
        in
        let generators =
          (match ft with
          | [] -> read_gens
          | _ -> TermGenerator (ms, ft) :: read_gens)
        in
        Binder (Forall, vs, ag bvs f, generators @ ann)
    | f -> f
  in
  ag IdSet.empty f
  (* end of add_generators *)

let mk_pred_vars svs = List.map (fun (x, srt) -> mk_var srt x) svs

let match_term_generator returns pred_vs name accesses (locals: Prog.var_decl Grass.IdMap.t) = 
  match returns with
  | [] ->
    let mt = mk_free_fun Bool name pred_vs in
    mt,
    if IdSet.mem name accesses
    then []
    else [TermGenerator ([Match (mt, [])], [mk_known mt])]
  | [x] ->
    let var = IdMap.find x locals in
    mk_free_fun var.var_sort name pred_vs, []
  | _ -> failwith "Functions may only have a single return value."

let rec add_match pred_match_term pred_vs m = function
  | Binder (b, vs, f, annots) ->
      let annots1 =
        List.map
          (function
            | TermGenerator (ms, ts) ->
                let not_var_match = function Match (t, _) -> not @@ List.mem t pred_vs in
                let ms1 = List.filter not_var_match ms in
                let ts1 = List.filter ((<>) pred_match_term &&& (<>) (mk_known pred_match_term)) ts in
                TermGenerator (m :: ms1, ts1)
            | a -> a)
          annots
      in
      Binder (b, vs, add_match pred_match_term pred_vs m f, annots1)
  | BoolOp (op, fs) ->
      BoolOp (op, List.map (add_match pred_match_term pred_vs m) fs)
  | f -> f

(** Generate axioms from predicate definitions *)
let pred_axioms prog =
  (* Annotates term generators in predicate bodies *)
  let annotate_term_generators pred f =
    let locals = locals_of_pred pred in
    let formals = formals_of_pred pred in
    let returns = returns_of_pred pred in
    let name = name_of_pred pred in
    let sorted_vs =
      List.map
        (fun x ->
          let var = IdMap.find x locals in
          x, var.var_sort)
        formals
    in
    let pred_vs = mk_pred_vars sorted_vs in
    let pred_match_term, generate_knowns =
      match_term_generator returns pred_vs name (accesses_pred pred) locals
    in
    let m = Match (mk_known pred_match_term, []) in
    annotate (add_match pred_match_term pred_vs m
      (add_generators prog (Some (name, m)) f)) generate_knowns
  in
  let pred_def pred =
    let locals = locals_of_pred pred in
    let formals = formals_of_pred pred in
    let returns = returns_of_pred pred in
    let name = name_of_pred pred in
    let sorted_vs, sm =
      List.fold_right
        (fun id (sorted_vs, sm) ->
          let var = IdMap.find id locals in
          (id, var.var_sort) :: sorted_vs,
          IdMap.add id (Var (id, var.var_sort)) sm
        )
        formals ([], IdMap.empty)
    in
    let defs =
      List.map
        (fun f -> f |> form_of_spec |> strip_error_msgs)
        (Opt.to_list pred.pred_body @ postcond_of_pred pred)
    in
    let defs =
      let rec split acc = function
        | Binder (Forall, vs, BoolOp (And, fs), a) :: ofs ->
            split acc (List.map (fun f -> Binder (Forall, vs, f, a)) fs @ ofs)
        | BoolOp (And, fs) :: ofs ->
            split acc (fs @ ofs)
        | f :: ofs -> split (f :: acc) ofs
        | [] -> List.rev acc
      in split [] defs
    in
    let vs = List.map (fun (id, srt) -> Var (id, srt)) sorted_vs in
    let sm, defs =
      match returns with
      | [] ->
          sm, List.map (fun f -> mk_implies (mk_pred name vs) f) defs            
      | [id] -> 
          let var = IdMap.find id locals in
          IdMap.add id (mk_free_fun var.var_sort name vs) sm, defs
      | _ -> failwith "Functions may only have a single return value."
    in
    let annot () =
      Name (fresh_ident @@ "definition_of_" ^ (string_of_ident name))
    in
    let pat =
      match returns with
      | [] -> [Pattern (mk_known (mk_free_fun Bool name vs), [])]
      | _ -> []
    in
    List.map (fun f ->
      f |>
      subst_consts sm |>
      smk_forall ~ann:(annot () :: pat) sorted_vs |>
      skolemize |>
      (*propagate_forall |>*)
      annotate_term_generators pred |>
      (if IdSet.mem name (accesses_pred pred)
      then (fun f -> f)
      else add_match_filters))
      defs
      (*(fun fs -> print_forms stdout fs; print_newline (); fs)*)
  in
  Prog.fold_preds (fun acc pred -> pred_def pred @ acc) [] prog

let pred_def_symb pred =
  let locals = locals_of_pred pred in
  let formals = formals_of_pred pred in
  let returns = returns_of_pred pred in
  let name = name_of_pred pred in
  let sorted_vs, sm =
    List.fold_right
      (fun id (sorted_vs, sm) ->
        let var = IdMap.find id locals in
        (id, var.var_sort) :: sorted_vs,
        IdMap.add id (Var (id, var.var_sort)) sm
      )
      formals ([], IdMap.empty)
  in
  let defs =
    List.map
      (fun f -> f |> form_of_spec |> strip_error_msgs)
      (Opt.to_list pred.pred_body @ postcond_of_pred pred)
  in
  let defs =
    let rec split acc = function
      | Binder (Forall, vs, BoolOp (And, fs), a) :: ofs ->
          split acc (List.map (fun f -> Binder (Forall, vs, f, a)) fs @ ofs)
      | BoolOp (And, fs) :: ofs ->
          split acc (fs @ ofs)
      | f :: ofs -> split (f :: acc) ofs
      | [] -> List.rev acc
    in split [] defs
  in
  let vs = List.map (fun (id, srt) -> Var (id, srt)) sorted_vs in
  let sm, defs =
    match returns with
    | [] ->
        sm, List.map (fun f -> mk_implies (mk_pred name vs) f) defs            
    | [id] -> 
        let var = IdMap.find id locals in
        IdMap.add id (mk_free_fun var.var_sort name vs) sm, defs
    | _ -> failwith "Functions may only have a single return value."
  in
  let annot () =
    Name (fresh_ident @@ "definition_of_" ^ (string_of_ident name))
  in
  let pat =
    match returns with
    | [] -> [Pattern (mk_known (mk_free_fun Bool name vs), [])]
    | _ -> []
  in
  List.map (fun f ->
    f |>
    subst_consts sm |>
    smk_forall ~ann:(annot () :: pat) sorted_vs |>
    skolemize |>
    (*propagate_forall |>*)
    (*annotate_term_generators pred |>*)
    (if IdSet.mem name (accesses_pred pred)
    then (fun f -> f)
    else add_match_filters))
    defs
    (*(fun fs -> print_forms stdout fs; print_newline (); fs)*)
 
(** Expand negative occurrences of predicates in formula [f] according to program [prog] and add term generators. *)
let finalize_form prog f =
  (* Expands definition of predicate [p] for arguments [ts] assuming polarity of occurrence [pol] *)
  let expand_pred pos p ts =
    let pred = find_pred prog p in
    let formals = formals_of_pred pred in
    let returns = returns_of_pred pred in
    let name = name_of_pred pred in
    let opt_body =
      match returns with
      | [] ->
          let sm =
            try
              List.fold_left2 
                (fun sm id t -> IdMap.add id t sm)
                IdMap.empty formals ts
            with Invalid_argument _ ->
              failwith ("Fatal error while expanding predicate " ^ string_of_ident name)
          in
          pred.pred_body |>
          Opt.map form_of_spec |>
          Opt.map (subst_consts sm)
        | [id] -> None
        | _ -> failwith "Functions may only have a single return value."
    in
    let body =
      Opt.get_or_else (Atom (mk_free_fun Bool p ts, [])) opt_body
    in
    if pos then body else nnf (mk_not body)
  in
  let f_inst = 
    let rec expand_neg msg_opt seen = function
      | Binder (b, vs, f, a) -> 
          Binder (b, vs, expand_neg msg_opt seen f, a)
      | BoolOp (And as op, fs)
      | BoolOp (Or as op, fs) ->
          let fs_inst = List.map (expand_neg msg_opt seen) fs in
          smk_op op fs_inst
      | BoolOp (Not, [Atom (App (FreeSym p, ts, _), a)])
        when IdMap.mem p prog.prog_preds && 
          not (IdSet.mem p seen) ->
            let pbody = expand_pred false p ts in
            let p_msg = ProgError.mk_error_info ("Definition of predicate " ^ (string_of_ident p)) in
            let a1 = 
              (*Label (false, mk_free_fun Bool p ts) ::*)
              match msg_opt with
              | Some msg ->
                  Util.partial_map (function SrcPos pos -> Some (ErrorMsg (pos, msg)) | _ -> None) a @ a
              | None -> a
            in
            let f1 = expand_neg (Some p_msg) (IdSet.add p seen) pbody in
            let f2 =
              if !Config.abstract_preds
              then mk_and [mk_not (Atom (mk_free_fun Bool p ts, [])); f1]
              else f1
            in
            annotate (annotate_aux_msg p_msg f2) a1
      | f -> f
    in
    f |>
    nnf |>
    expand_neg None IdSet.empty |>
    (*fun f -> print_endline "before: "; print_form stdout f; print_newline(); f |> *)
    foralls_to_exists |>
    (*fun f -> print_endline "after: "; print_form stdout f; print_newline(); f |> *)
    propagate_forall_down |>
    propagate_exists_up |>
    SimplifyGrass.simplify_one_sets |>
    foralls_to_exists |>
    skolemize |>
    add_generators prog None |>
    add_match_filters
      (*|> fun f -> print_endline "after: "; print_form stdout f; print_newline(); f*)
  in
  f_inst
  
(** Generate verification conditions for procedure [proc] of program [prog]. 
 ** Assumes that [proc] has been transformed into SSA form. *)
let vcgen prog =
  let spec_forms_to_forms =
    Util.flat_map 
      (fun sf -> 
        let name = 
          Printf.sprintf "%s_%d_%d" 
            sf.spec_name sf.spec_pos.sp_start_line sf.spec_pos.sp_start_col
        in
        match sf.spec_form with
        | FOL f ->
            let f1 = f |> mk_name name in
            [f1]
        | SL _ -> [])
  in
  let axiom_from_lemma proc =
    let locals = locals_of_proc proc in
    let formals = formals_of_proc proc in
    let returns = returns_of_proc proc in
    let _ = assert (returns = []) in
    let _name = name_of_proc proc in
    let sorted_vs, sm =
      List.fold_right
        (fun id (sorted_vs, sm) ->
          let var = IdMap.find id locals in
          (id, var.var_sort) :: sorted_vs,
          IdMap.add id (Var (id, var.var_sort)) sm
        )
        formals ([], IdMap.empty)
    in
    let pre_conds = spec_forms_to_forms (precond_of_proc proc) in
    let post_conds = spec_forms_to_forms (postcond_of_proc proc) in
    mk_forall sorted_vs (mk_sequent pre_conds [mk_and post_conds] |> subst_consts sm)
  in
  let assumed_auto_lemmas =
    prog.prog_procs |>
    IdMap.bindings |>
    Util.filter_map (fun (_, proc) -> proc.proc_is_auto && proc.proc_body = None) snd
  in
  let axioms =
    spec_forms_to_forms prog.prog_axioms
    @
      List.map axiom_from_lemma assumed_auto_lemmas
    @
      pred_axioms prog
  in
  fun aux_axioms proc ->
    let proc_name = name_of_proc proc in
    let rec vcs acc pre = function
      | Loop _ -> 
          failwith "vcgen: loop should have been desugared"
      | Choice (cs, pp) ->
          let acc1, traces = 
            List.fold_left (fun (acc, traces) c ->
              let acc1, trace = vcs acc pre c in
              acc1, trace :: traces)
              (acc, []) cs
          in acc1, [smk_or (List.rev_map smk_and traces)]
      | Seq (cs, pp) -> 
          let acc1, trace, _ = 
            List.fold_left (fun (acc, trace, pre) c ->
              let acc1, c_trace = vcs acc pre c in
              acc1, trace @ c_trace, pre @ c_trace)
              (acc, [], pre) cs 
          in
          acc1, trace
      | Basic (bc, pp) ->
          match bc with
          | Assume s ->
              let name = 
                Printf.sprintf "%s_%d_%d" 
                  s.spec_name pp.pp_pos.sp_start_line pp.pp_pos.sp_start_col
              in
              (match s.spec_form with
              | FOL f -> acc, [mk_name name (unoldify_form f)]
              | _ -> failwith "vcgen: found SL formula that should have been desugared")
          | Assert s ->
              let vc_name, name = 
                if Opt.map ((=) s.spec_name) !Config.assertion |> Opt.get_or_else false
                then s.spec_name, s.spec_name
                else
                  let name =
                    Printf.sprintf "%s_%d_%d" 
                      s.spec_name pp.pp_pos.sp_start_line pp.pp_pos.sp_start_col
                  in
                  Str.global_replace (Str.regexp " ") "_"
                    (string_of_ident proc_name ^ "_" ^ name), name
              in
              let vc_msg, vc_aux_msg = 
                match s.spec_msg with
                | None -> 
                    "Possible assertion violation.", 
                    ProgError.mk_error_info "This is the assertion that might be violated"
                | Some msg -> msg proc_name
              in 
              let vc_msg = (vc_msg, pp.pp_pos) in
              let f =
                match s.spec_form with
                | FOL f ->
                    let f1 = unoldify_form (mk_not f) in
                    let f2 = annotate_aux_msg vc_aux_msg f1 in
                    f2
                | _ -> failwith "vcgen: found SL formula that should have been desugared"
              in
              let vc = pre @ [mk_name name f] in
              let vc_and_preds = finalize_form prog (smk_and vc) in
              let labels, vc_and_preds = add_labels vc_and_preds in
              (vc_name, vc_msg, smk_and (axioms @ aux_axioms @ [vc_and_preds]), labels) :: acc, []
          | _ -> 
              failwith "vcgen: found unexpected basic command that should have been desugared"
    in
    let aux_axioms1 =
      if proc.proc_is_auto then
        [axiom_from_lemma proc]
      else []
        @ aux_axioms
    in
    match proc.proc_body with
    | Some body ->
        aux_axioms1, List.rev (fst (vcs [] [] body))
    | None -> aux_axioms1, []

(** Generate error message from labels in the model *)
let get_err_msg_from_labels model labels =
  let add_msg pos msg error_msgs =
    let filtered_msgs = 
      List.filter 
        (fun (pos2, _) -> not (contained_in_src_pos pos pos2))
        error_msgs
    in
    (pos, msg) :: filtered_msgs
  in
  let error_msgs = 
    IdMap.fold 
      (fun id (pos, msg) error_msgs ->
        let p = mk_free_const Bool id in
        match Model.eval_bool model p with
        | Some true ->
            add_msg pos msg error_msgs
        | _ -> error_msgs
      ) 
      labels []
  in
  let sorted_error_msgs = 
    List.sort
      (fun (pos1, msg1) (pos2, msg2) -> 
        let mc = 
          compare (String.get msg1 0) (String.get msg2 0) 
        in
        if mc = 0 then compare_src_pos pos1 pos2 else mc) 
      error_msgs
  in
  List.map 
    (fun (pos, msg) -> ProgError.error_to_string pos msg) 
    sorted_error_msgs

(** Generate verification conditions for procedure [proc] of program [prog] and check them. *)
let check_proc prog =
  let vcgen = vcgen prog in
  fun aux_axioms proc ->
  let check_vc errors (vc_name, (vc_msg, pp), vc0, labels) =
    let check_one vc =
      let is_requested_assert =
        !Config.assertion |> Opt.map ((=) vc_name) |> Opt.get_or_else true
      in
      if errors <> [] && not !Config.robust || not is_requested_assert
      then errors
      else begin
        Debug.info (fun () -> "\t" ^ vc_name ^ ".\n");
        Debug.debug (fun () -> (string_of_form vc) ^ "\n");
      (*IdMap.iter (fun id (pos, c) -> Printf.printf ("%s -> %s: %s\n") 
         (string_of_ident id) (string_of_src_pos pos) c) labels;*)
        let sat_means = 
          Str.global_replace (Str.regexp "\n\n") "\n  " (ProgError.error_to_string pp vc_msg)
        in
        let session_name =
          Filename.chop_extension (Filename.basename pp.sp_file) ^ "_" ^ vc_name 
        in
        match Prover.get_model ~session_name:session_name ~sat_means:sat_means vc with
        | None -> errors
        | Some model -> 
            let error_msg =
              String.concat "\n\n" (vc_msg :: get_err_msg_from_labels model labels)
            in
            (pp, error_msg, model) :: errors
      end
    in check_one vc0
  in
  let _ = Debug.info (fun () ->
    "Checking " ^ (if proc.proc_is_lemma then "lemma " else "procedure ") ^
    string_of_ident (name_of_proc proc) ^ "...\n")
  in
  let aux_axioms, vcs = vcgen aux_axioms proc in
  aux_axioms, List.fold_left check_vc [] vcs

(** Generate a counterexample trace from a failed VC of procedure [proc] in [prog]. 
  * Here [pp] is the point of failure in [proc] and [model] is the counterexample model. *)
let get_trace prog proc (pp, model) =
  let add (pos, state) = function
    | (prv_pos, prv_state) :: trace ->
        if prv_pos = pos 
        then (prv_pos, prv_state) :: trace
        else (pos, state) :: (prv_pos, prv_state) :: trace
    | [] -> [(pos, state)]
  in
  let rec update_vmap (vmap, all_aux) = function
    | Atom (App (Eq, [App (FreeSym (name, num), [], _); _], _), _) ->
        let decl = find_var prog proc (name, num) in
        IdMap.add (name, 0) (name, num) vmap,
        decl.var_is_aux && all_aux
    | BoolOp (And, fs) ->
        List.fold_left update_vmap (vmap, all_aux) fs
    | Binder (_, [], f, _) -> 
        update_vmap (vmap, all_aux) f
    | _ -> vmap, all_aux
  in
  let get_curr_state pos vmap model =
    let ids = 
      IdMap.fold 
        (fun _ id ids -> 
          let decl = find_var prog proc id in
          if decl.var_is_aux && name id <> "FP" && name id <> "Alloc" || 
             not (contained_in_src_pos pos decl.var_scope) 
          then ids
          else IdSet.add id ids) 
        vmap IdSet.empty 
    in
    let rmodel = Model.restrict_to_idents model ids in
    Model.rename_free_symbols rmodel (fun (name, _) -> (name, 0))
  in
  let rec gt vmap trace = function
    | Choice (cs, pp) :: cs1 ->
        Util.flat_map (gt vmap trace) (List.map (fun c -> c :: cs1) cs)
    | Seq (cs, pp) :: cs1 -> 
        gt vmap trace (cs @ cs1)
    | Basic (bc, _)  :: cs1 ->
        (match bc with
        | Assume s ->
            (match s.spec_name with
            | "assign" | "if_then" | "if_else" | "havoc" ->
                let f = form_of_spec s in
                (match Model.eval_form model f with
                | None -> 
                    (*print_string "Ignoring command: ";
                    print_endline (Grass.string_of_src_pos s.spec_pos);
                    Prog.print_cmd stdout c;
                    print_newline ();*)
                    gt vmap trace cs1
                | Some true -> 
                    (*print_string "Adding command: ";
                    print_endline (Grass.string_of_src_pos s.spec_pos);
                    Prog.print_cmd stdout c;
                    print_newline ();*)
                    let curr_state = get_curr_state s.spec_pos vmap model in
                    if s.spec_name = "assign" || s.spec_name = "havoc"
                    then 
                      let vmap1, all_aux = update_vmap (vmap, true) f in
                      let trace1 = 
                        if all_aux 
                        then trace 
                        else add (s.spec_pos, curr_state) trace
                      in
                      gt vmap1 trace1 cs1
                    else gt vmap (add (s.spec_pos, curr_state) trace) cs1
                | Some false -> 
                    (* print_string "Dropping trace on assume: ";
                    print_endline (Grass.string_of_src_pos s.spec_pos);
                    Prog.print_cmd stdout c;
                    print_newline (); *)
                    [])
            | "join" -> 
                let vmap1, _ = update_vmap (vmap, true) (form_of_spec s) in
                gt vmap1 trace cs1
            | _ -> gt vmap trace cs1)
        | Assert s ->
            if pp = s.spec_pos
            then 
              let curr_state = get_curr_state pp vmap model in
              List.rev ((pp, curr_state) :: trace)
            else gt vmap trace cs1
        | _ -> gt vmap trace cs1)
    | _ :: cs1 -> gt vmap trace cs1
    | [] -> 
        let curr_state = get_curr_state pp vmap model in
        List.rev ((pp, curr_state) :: trace)
  in 
  let init_vmap =
    let vars = IdMap.merge (fun id v1 v2 ->
      match v1, v2 with
      | Some v1, _ -> Some v1
      | _, Some v2 -> Some v2
      | _, _ -> None) prog.prog_vars (locals_of_proc proc)
    in
    IdMap.fold 
      (fun (name, num) _ vmap -> 
        try 
          if snd (IdMap.find (name, 0) vmap) > num 
          then IdMap.add (name, 0) (name, num) vmap
          else vmap
        with Not_found -> IdMap.add (name, 0) (name, num) vmap)
      vars IdMap.empty
  in
  match gt init_vmap [] (Util.Opt.to_list proc.proc_body) with
  | _ :: trace -> trace
  | [] -> []
