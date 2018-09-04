(** E-Matching.

  Implements a variant of the e-matching technique presented in this paper:
      Efficient E-Matching for SMT Solvers
      Leonardo de Moura and Nikolaj Bjorner, CADE 2007

*)

open Util
open Grass
open GrassUtil

module CC = CongruenceClosure

(** E-matching code trees *)
type 'a ematch_code =
  | Init of TermSet.t * sorted_symbol * int * 'a ematch_code
  | Bind of int * sorted_symbol * int * 'a ematch_code
  | Check of int * term * 'a ematch_code
  | Compare of int * int * 'a ematch_code
  | Choose of 'a ematch_code list
  | Yield of int IdMap.t * 'a list
  | Prune of int * sorted_symbol * 'a ematch_code
  | Filter of (int IdMap.t * filter list) TermMap.t * 'a ematch_code
  | ChooseApp of int * 'a ematch_code * CC.Node.t list list

(** Pretty printing of E-matching code trees *)
open Format

let pr_var_binding ppf (x, i) =
  fprintf ppf "%a -> %d" pr_ident x i

let pr_ematch_code pr_inst ppf =
  let rec pr_ematch_code ppf = function
    | Choose cs ->
        fprintf ppf "@<-3>%s@ %a" "choose" pr_choose cs
    | Init (ts, sym, i, next) ->
        fprintf ppf "init(@[%a,@ %d@])@\n%a" pr_term_list (TermSet.elements ts) i pr_ematch_code next
    | Bind (i, sym, o, next) ->
        fprintf ppf "bind(@[%d,@ %a,@ %d@])@\n%a" i pr_sym (fst sym) o pr_ematch_code next
    | Check (i, t, next) ->
        fprintf ppf "check(@[%d,@ %a@])@\n%a" i pr_term t pr_ematch_code next
    | Compare (i, j, next) ->
        fprintf ppf "compare(@[%d,@ %d@])@\n%a" i j pr_ematch_code next
    | Yield (vs, fs) ->
        fprintf ppf "@[<2>yield(@[[%a]@]) ->@\n%a@]" (pr_list_comma pr_var_binding) (IdMap.bindings vs)
          (pr_list 0
             (fun ppf _ -> fprintf ppf ",@\n")
             (fun i ppf f -> fprintf ppf "@[<2>%2d:@ %a@]" i pr_inst f))  fs
    | Prune (i, sym, next) ->
        fprintf ppf "prune(@[%d,@ %a@])@\n%a" i pr_sym (fst sym) pr_ematch_code next
    | Filter (filters, next) ->
        fprintf ppf "filter(@[%a@])@\n%a"
          pr_term_list (filters |> TermMap.bindings |> List.map fst)
          (*(pr_list_comma pr_var_binding) (IdMap.bindings vs)
            pr_term t
            pr_filter filters*)
          pr_ematch_code next
    | ChooseApp (i, next, _) ->
        fprintf ppf "chooseApp(@[%d@])@\n%a" i pr_ematch_code next
        
  and pr_choose ppf = function
    | [] -> ()
    | [c] -> fprintf ppf "{@[<1>@\n%a@]@\n}" pr_ematch_code c
    | c :: cs -> fprintf ppf "{@[<1>@\n%a@]@\n}@ @ @<-3>%s@ %a" pr_ematch_code c "or" pr_choose cs
  in pr_ematch_code ppf
          
let print_ematch_code string_of_inst out_ch code =
  print_of_format (pr_ematch_code string_of_inst) code out_ch
        
(** A few utility functions *)

(** Get the continuation of the first command *)
let continuation = function
  | Init (_, _, _, next)
  | Bind (_, _, _, next)
  | Check (_, _, next)
  | Compare (_, _, next)
  | Filter (_, next) -> next
  | _ -> failwith "illegal argument to continuation"

(** Get the maximum register in code tree c, yields -1 if c uses no registers *)
let max_reg c =
  let rec mr m = function
    | Init (_, _, i, c) 
    | Check (i, _, c)
    | ChooseApp (i, c, _) -> mr (max m i) c
    | Filter (_, c)
    | Prune (_, _, c) -> mr m c
    | Bind (i, _, j, c)
    | Compare (i, j, c) -> mr (max (max m i) j) c
    | Choose cs ->
        List.fold_left mr m cs
    | Yield (vs, _) -> IdMap.fold (fun _ -> max) vs m
  in
  mr (-1) c

(** Make a choice tree out of trees c1 and 
  * Avoids the creation of nested choice nodes. *)
let mk_choose c1 c2 =
  match c1, c2 with
  | Choose cs1, Choose cs2 -> Choose (cs1 @ cs2)
  | Choose cs1, _ -> Choose (cs1 @ [c2])
  | _, Choose cs2 -> Choose (c1 :: cs2)
  | _ -> Choose [c1; c2]

(** Work queue for pattern compilation *)
module WQ = PrioQueue.Make
    (struct
      type t = int
      let compare = compare
    end)
    (struct
      type t = term
      let compare t1 t2 =
        (* Rational for the following definition: 
         * process entries i -> x and i -> t where t is ground before entries i -> f(t_1, ..., t_n)
         * in order to delay the creation of branching nodes. *)
        if is_ground_term t1 && not @@ is_ground_term t2 then -1
        else match t1, t2 with
        | Var _, App _ -> -1
        | App _, Var _ -> 1
        | _ -> compare t1 t2  
    end)

(** Compile the list of patterns [patterns] into an ematching code tree *)
let compile patterns =
  let add_args_to_queue w o args =
    List.fold_left
      (fun (w', o') arg -> WQ.insert o' arg w', o' + 1)
      (w, o) args
  in
  let prune args o next =
    let code, _ =
      List.fold_left
        (fun (next, o) -> function
          | App (sym, _, _) as t when not @@ is_ground_term t ->
              Prune (o, sorted_symbol_of t |> Opt.get, next), o + 1
          | _ -> next, o + 1)
        (next, o) args
    in
    code
  in
  (* Compile a (multi-)pattern into a code tree.
   * f: info about current term of the multi-pattern that is being processed.
   * pattern: remaining terms of the multi-pattern that still need to be processed.
   * w: work queue of subterms of [f] that still need to be processed.
   * v: accumulated map of variable to register bindings.
   * o: number of next unused register.
   *)
  let rec compile f pattern w v o =
    let rec c w v o =
      if WQ.is_empty w then match f with
      | (f, filters_opt) ->
          let next = init f pattern v o in
          Opt.fold (fun n -> function
            | t, (_ :: _ as fs) ->
                let filters = TermMap.singleton t (v, fs) in
                Filter (filters, n)
            | _ -> n) next
            filters_opt
      else
      let i, t, w' = WQ.extract_min w in
      match t with
      | Var (x, _) when not @@ IdMap.mem x v ->
          c w' (IdMap.add x i v) o
      | Var (x, _) ->
          let next = c w' v o in
          let j = IdMap.find x v in
          if i = j then next
          else Compare (i, j, next)
      | t when is_ground_term t ->
          Check (i, t, c w' v o)
      | App (sym, args, _) ->
          let w'', o' = add_args_to_queue w' o args in
          let next = prune args o (c w'' v o') in
          Bind (i, sorted_symbol_of t |> Opt.get, o, next)
    in
    c w v o
  and init f pattern v o =
    match pattern with
    | (App (_, args, _) as t, filters) :: pattern ->
        let ts = TermSet.singleton t in
        let w, o' = add_args_to_queue WQ.empty o args in
        let next = prune args o (compile (f, Some (t, filters)) pattern w v o') in
        Init (ts, sorted_symbol_of t |> Opt.get, o, next)
    | (Var _, _) :: _ -> failwith "TODO"
    | [] ->
        Yield (v, [f])
  in
  let seq cs fchild =
    let rec s = function
      | Init (ts, sym, o, c) :: cs -> Init (ts, sym, o, s cs)
      | Check (i, t, c) :: cs -> Check (i, t, s cs)
      | Compare (i, j, c) :: cs -> Compare (i, j, s cs)
      | Bind (i, sym, o, c) :: cs -> Bind (i, sym, o, s cs)
      | Prune (i, fs, c) :: cs -> Prune (i, fs, s cs)
      | Filter (filters, c) :: cs -> Filter (filters, s cs)
      | [] -> fchild
      | _ -> assert false
    in
    s (List.rev cs)
  in
  let branch f pattern comps fchild w v o =
    seq comps (mk_choose (compile f pattern w v o) fchild)
  in
  let check_if_queue_processed w v =
    WQ.fold
      (fun i t (v', fully_processed) ->
        match t with
        | App _ -> v', false
        | Var (x, _) ->
            IdMap.add x i v',
            fully_processed && (IdMap.find_opt x v' |> Opt.get_or_else i |> (=) i)
      )
      w (v, true)
  in
  (* Check whether [(f, pattern, w, v)] is compatible with the first node of [code].
   * If yes, return updated values [(code', w', v', f', pattern')]. *)
  let compatible f pattern w v code = 
    match code with
    | Init (ts, sym, o, next) ->
        (* Has w been fully processed? *)
        let v', fully_processed = check_if_queue_processed w v in
        if fully_processed then 
          match pattern with
          | (App (_, args, _) as t, filters) :: pattern'
            when sorted_symbol_of t = Some sym ->
              let w', _ = add_args_to_queue WQ.empty o args in
              let f' = (fst f, Some (t, filters)) in
              let code' = Init (TermSet.add t ts, sym, o, next) in
              Some (code', w', v', f', pattern')
          | _ -> None
        else None
    | Filter (filters, next) ->
        (match f with
        | inst, Some (t, fs) ->
            let v' =
              WQ.fold
                (fun i t v -> match t with
                | Var (x, _) -> IdMap.add x i v
                | _ -> v)
                w IdMap.empty
            in
            let filters' = TermMap.add t (v', fs) filters in
            Some (Filter (filters', next), w, v, (inst, None), pattern)
        | _, None -> None)
    | Check (i, t, _) ->
        (match WQ.find_opt i w with
        | Some t' when t = t' -> Some (code, WQ.delete i w, v, f, pattern)
        | _ -> None)
    | Compare (i, j, _) ->
        let ti_opt = WQ.find_opt i w in
        (match ti_opt with
        | Some (Var (x, _) as ti) ->
            let v'_opt = match WQ.find_opt j w with
            | Some tj when ti = tj -> Some (IdMap.add x j v)
            | None when IdMap.find_opt x v = Some j -> Some v
            | _ -> None
            in
            Opt.map (fun v' -> code, WQ.delete i w, v', f, pattern) v'_opt
        | _ -> None)
    | Bind (i, sym, o, _) ->
        (match WQ.find_opt i w with
        | Some (App (_, args, _) as t) when sorted_symbol_of t = Some sym ->
            let w', _ = add_args_to_queue w o args in
            Some (code, WQ.delete i w', v, f, pattern)
        | _ -> None)
    | _ -> None
  in
  let rec insert_code f pattern w v o comps incomps code =
    match code with
    | Choose cs ->
        if incomps = [] then
          let code', score = insert_choose f pattern cs w v o in
          seq comps code', score + List.length comps
        else branch f pattern comps (seq incomps code) w v o, List.length comps
    | Yield (v1, fs) ->
        let v2, fully_processed = check_if_queue_processed w v in
        let v1_union_v2 = IdMap.union (fun x i j -> Some i) v1 v2 in
        let v2_union_v1 = IdMap.union (fun x i j -> Some j) v1 v2 in
        let filters = snd f |> Opt.map snd |> Opt.get_or_else [] in
        if incomps = [] && pattern = [] && fully_processed && filters = [] && IdMap.equal (=) v1_union_v2 v2_union_v1
        then seq comps (Yield (v1_union_v2, fst f :: fs)), List.length comps + 1
        else branch f pattern comps (seq incomps code) w v o, List.length comps
    | Prune _ ->
        branch f pattern comps (seq incomps code) w v o, List.length comps
    | code ->
        let next = continuation code in
        compatible f pattern w v code |>
        Opt.map (fun (code', w', v', f', pattern') ->
          insert_code f' pattern' w' v' o (code' :: comps) incomps next) |>
        Opt.lazy_get_or_else (fun () -> insert_code f pattern w v o comps (code :: incomps) next)
  and insert_choose f pattern cs w v o =
    let cs', _, best =
      List.fold_right
        (fun code (cs', cs, best) ->
          match insert_code f pattern w v o [] [] code with
          | code', score when score > best ->
              code' :: cs, code :: cs, score
          | _ -> code :: cs', code :: cs, best
        )
        cs ([], [], 0) 
    in
    if best = 0
    then Choose (compile f pattern w v o :: cs), 0
    else Choose cs', best
  in   
  List.fold_left
    (fun code (f, pattern) ->
      let code', _ = insert_code (f, None) pattern WQ.empty IdMap.empty (max_reg code + 1) [] [] code in
      code'
    )
    (Choose []) patterns

(** Generate an E-matching code tree from the given set of axioms. *)
let generate_ematch_code_from_axioms ?(force=false) ?(stratify=(!Config.stratify)) axioms = 
  (* *)
  let epr_axioms, axioms = 
    List.partition 
      (fun f -> IdSrtSet.is_empty (vars_in_fun_terms f) || not !Config.instantiate && not force) 
      axioms
  in
  (*print_endline "EPR:";
    List.iter print_endline (List.map string_of_form epr_axioms);*)
  (*let _ = print_endline "Candidate axioms for instantiation:" in
    let _ = print_forms stdout axioms in*)
  let generate_pattern f =
    let fvars0 = sorted_free_vars f in
    let fvars = IdSrtSet.inter fvars0 (vars_in_fun_terms f) in
    (* filter out stratified variables *)
    let fvars, strat_vars =
      let merge_map k a b = match (a,b) with
        | (Some a, Some b) -> Some (a @ b)
        | (Some c, None) | (None, Some c) -> Some c
        | (None, None) -> None 
      in
      let rec gen_tpe acc t = match t with
      | App (_, ts, srt) ->
          List.fold_left
            (IdMap.merge merge_map)
            IdMap.empty
            (List.map (gen_tpe (srt :: acc)) ts)
      | Var (id, _) -> IdMap.add id acc IdMap.empty
      in
      let gen_map =
        TermSet.fold
          (fun t acc -> IdMap.merge merge_map (gen_tpe [] t) acc)
          (fun_terms_with_vars f)
          IdMap.empty
      in
        if stratify then
          IdSrtSet.partition
            (fun (id, srt) ->
              try
                let generating = IdMap.find id gen_map in
                  not (List.for_all (TypeStrat.is_stratified srt) generating)
              with Not_found ->
                begin
                  Debug.warn (fun () -> "BUG in stratification: " ^ (string_of_ident id) ^ "\n");
                  true
                end
            )
            fvars
        else fvars, IdSrtSet.empty
    in
    let strat_var_ids = IdSrtSet.fold (fun (id, _) acc -> IdSet.add id acc) strat_vars IdSet.empty in 
    (* collect all terms in which free variables appear below function symbols *)
    let fun_terms, fun_vars, strat_terms = 
      let rec tt (fun_terms, fun_vars, strat_terms) t =
        match t with
        | App (sym, _ :: _, srt) when srt <> Bool ->
            let tvs = fv_term t in
            if IdSet.is_empty tvs then
              fun_terms, fun_vars, strat_terms
            else if IdSet.is_empty (IdSet.inter strat_var_ids tvs)
            then TermSet.add t fun_terms, IdSet.union tvs fun_vars, strat_terms
            else fun_terms, fun_vars, TermSet.add t strat_terms
        | App (_, ts, _) ->
            List.fold_left tt (fun_terms, fun_vars, strat_terms) ts
        | _ -> fun_terms, fun_vars, strat_terms
      in fold_terms tt (TermSet.empty, IdSet.empty, TermSet.empty) f
    in
    let unmatched_vars =
      IdSrtSet.fold (fun (id, _) acc ->
        if IdSet.mem id fun_vars then acc
        else IdSet.add id acc) fvars IdSet.empty
    in
    let fun_terms, fun_vars =
      TermSet.fold (fun t (fun_terms, fun_vars) ->
        let vs = fv_term t in
        if IdSet.is_empty (IdSet.inter unmatched_vars vs)
        then fun_terms, fun_vars
        else TermSet.add t fun_terms, IdSet.union vs fun_vars)
        strat_terms (fun_terms, fun_vars)
    in
    let strat_vars1 =
      IdSrtSet.filter (fun (id, _) -> not (IdSet.mem id fun_vars)) strat_vars
    in
    (* extract patterns separately to obtain auxilary filters *)
    let patterns = extract_patterns f in
    let fun_terms_with_filters =
      TermSet.fold (fun t acc ->
        try (t, List.assoc t patterns) :: acc
        with Not_found -> (t, []) :: acc)
        fun_terms []
    in
    let fun_terms_with_filters =
      List.sort (fun (t1, _) (t2, _) ->
        - (compare
             (IdSet.cardinal (fv_term t1))
             (IdSet.cardinal (fv_term t2))))
        fun_terms_with_filters
    in
    let f = mk_forall (IdSrtSet.elements strat_vars1) f in
    (f, fvars0, strat_vars1, unmatched_vars, fun_vars, fun_terms_with_filters), fun_terms_with_filters
  in
  let patterns = [] in
  let patterns = List.fold_right (fun f patterns -> ((f, IdSrtSet.empty, IdSrtSet.empty, IdSet.empty, IdSet.empty, []), []) :: patterns) epr_axioms patterns in
  let patterns = List.fold_right (fun f patterns -> generate_pattern f :: patterns) axioms patterns in
  compile patterns, patterns
    
(** Run the given e-matching code tree. Yields a list of instantiated formulas. *)
let run code ccgraph =
  let egraph = CC.get_egraph ccgraph in
  let get_apps sym =
    CC.EGraph.fold
      (fun (n, sym') n_apps apps ->
        if sym = sym'
        then CC.NodeListSet.union n_apps apps
        else apps)
      egraph CC.NodeListSet.empty |>
    CC.NodeListSet.elements
  in
  let get_apps_of_node n sym =
    CC.EGraph.find_opt (n, sym) egraph |>
    Opt.get_or_else CC.NodeListSet.empty |>
    CC.NodeListSet.elements
  in
  let regs = Array.make (max_reg code + 1) (CC.rep_of_term ccgraph mk_true_term) in
  let insts = Hashtbl.create 1000 in
  let rec run ts = function
    | Init (ts, sym, o, next) :: stack ->
        let apps = get_apps sym in
        run ts (ChooseApp (o, next, apps) :: stack)
    | Bind (i, sym, o, next) :: stack ->
        let apps = get_apps_of_node (regs.(i)) sym in
        run ts (ChooseApp (o, next, apps) :: stack)
    | Check (i, t, next) :: stack ->
        if CC.rep_of_term ccgraph t = regs.(i)
        then run ts (next :: stack)
        else run ts stack
    | Compare (i, j, next) :: stack ->
        if regs.(i) = regs.(j)
        then run ts (next :: stack)
        else run ts stack
    | Choose cs :: stack ->
        run ts (cs @ stack)
    | Yield (vs, fs) :: stack ->
        let sm = IdMap.map (fun i -> CC.term_of_rep ccgraph regs.(i)) vs in
        List.iter (fun f -> Hashtbl.add insts f sm) fs;
        run ts stack
    | Prune (i, sym, next) :: stack ->
        let n = regs.(i) in
        if BloomFilter.mem sym (CC.funs_of_rep ccgraph n)
        then run ts (next :: stack)
        else run ts stack
    | Filter (filters, next) :: stack ->
        let ts' =
          TermSet.filter
            (fun t ->
              let t_filters = TermMap.find_opt t filters in
              match t_filters with
              | Some (vs, fs) ->
                  let sm = IdMap.map (fun i -> CC.term_of_rep ccgraph regs.(i)) vs in
                  InstGen.filter_term fs (subst_term sm t) sm
              | None -> true)
            ts
        in
        if TermSet.is_empty ts'
        then run ts stack
        else run ts' (next :: stack)
    | ChooseApp (o, next, args :: apps) :: stack ->
        let _ =
          List.fold_left
            (fun i arg -> regs.(i) <- arg; i + 1)
            o args
        in
        run ts (next :: ChooseApp (o, next, apps) :: stack)
    | ChooseApp (_, _, []) :: stack ->
        run ts stack
    | [] -> insts
  in
  run TermSet.empty [code]

let instantiate_axioms_from_code patterns code ccgraph =
  let _ =
    if Debug.is_debug 1 then CC.print_classes ccgraph
  in
  let instances = run code ccgraph in
  let get_form (f, _, _, _, _, _) = f in
  let print_debug ((f, fvars, strat_vars, unmatched_vars, fun_vars, fun_terms_with_filters), subst_maps) =
    print_endline "--------------------";
    print_endline (string_of_form f);
    print_string "all vars: ";
    flush stdout;
    print_list stdout pr_ident (List.map fst (IdSrtSet.elements fvars));
    print_newline ();
    print_string "strat vars: ";
    print_list stdout pr_ident (List.map fst (IdSrtSet.elements strat_vars));
    print_newline ();
    print_string "unmatched vars: ";
    print_list stdout pr_ident (IdSet.elements unmatched_vars);
    print_newline ();
    print_string "inst vars: ";
    print_list stdout pr_ident (IdSet.elements fun_vars);
    print_newline ();
    print_string "fun terms: ";
    print_list stdout pr_term (List.map fst fun_terms_with_filters);
    print_newline ();
    Printf.printf "# of insts: %d\n" (List.length subst_maps);
    print_endline "subst_maps:";
    List.iter print_subst_map subst_maps;
    print_endline "--------------------";
  in
  let grouped_instances =
    List.rev_map
      (fun (f, _) ->
        let sms = Hashtbl.find_all instances f in
        (f, sms))
      patterns
  in
  let _ =
    if Debug.is_debug 1 then begin
      grouped_instances |>
      List.rev_map (fun (f, sms) -> (f, List.filter ((<>) IdMap.empty) sms)) |>
      List.iter print_debug
    end
  in
  grouped_instances |>
  List.fold_left
    (fun instances (f_aux, sms) ->
      List.fold_left (fun instances sm ->
        subst sm (get_form f_aux) :: instances)
        instances sms) []

let instantiate_axioms_from_code patterns code ccgraph =
  measure_call "EMatching.instantiate_axioms" (instantiate_axioms_from_code patterns code) ccgraph

let instantiate_axioms ?(force=false) ?(stratify=(!Config.stratify)) axioms ccgraph =
  let code, patterns = generate_ematch_code_from_axioms ~force:force ~stratify:stratify axioms in
  instantiate_axioms_from_code patterns code ccgraph
    
