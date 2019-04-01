(** {5 Utility functions for manipulating GRASS formulas}*)

open Grass
open Util

(** {6 Auxiliary functions for manipulating source positions} *)

let dummy_position = 
  { sp_file = "";
    sp_start_line = max_int;
    sp_start_col = max_int;
    sp_end_line = 0;
    sp_end_col = 0 
  }

let global_scope =
  { sp_file = "";
    sp_start_line = 0;
    sp_start_col = 0;
    sp_end_line = max_int; 
    sp_end_col = max_int;
  }

let merge_src_pos pos1 pos2 =
  (*assert (pos1.sp_file = "" || pos2.sp_file = "" || pos1.sp_file = pos2.sp_file);*)
  let file = max pos1.sp_file pos2.sp_file in
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
  { sp_file = file;
    sp_start_line = start_line;
    sp_start_col = start_col;
    sp_end_line = end_line;
    sp_end_col = end_col;
  }

let in_same_file pos1 pos2 = 
  pos1.sp_file = "" ||
  pos2.sp_file = "" ||
  pos1.sp_file = pos2.sp_file

let starts_before_src_pos pos1 pos2 =
  in_same_file pos1 pos2 &&
  (pos1.sp_start_line < pos2.sp_start_line || 
   pos1.sp_start_line = pos2.sp_start_line && pos1.sp_start_col <= pos2.sp_start_col)
  
let ends_before_src_pos pos1 pos2 =
  in_same_file pos1 pos2 &&
  (pos1.sp_end_line < pos2.sp_end_line || 
  pos1.sp_end_line = pos2.sp_end_line && pos1.sp_end_col <= pos2.sp_end_col)

let contained_in_src_pos pos1 pos2 =
  starts_before_src_pos pos2 pos1 && ends_before_src_pos pos1 pos2    
  
let compare_src_pos pos1 pos2 =
  let cf = compare pos1.sp_file pos2.sp_file in
  if cf <> 0 then cf else
  if starts_before_src_pos pos1 pos2 then
    if starts_before_src_pos pos2 pos1 then 0
    else -1
  else 1

(** {6 Equality on formulas} *)

(** Equality test on formulas. Compares formulas modulo alpha renaming, 
  * stripping of annotations, etc. *)
let equal f1 f2 =
  (* The pair of maps (sm1, sm2) represents a bijection between the 
   * bound variables in f1 and f2. This bijection is constructed on the fly 
   * to prove alpha equivalence. *)
  let rec forall2 fn sm1 sm2 xs ys =
    match xs, ys with
    | x :: xs, y :: ys ->
        let sm1, sm2, b = fn sm1 sm2 x y in
        if b then forall2 fn sm1 sm2 xs ys
        else sm1, sm2, b
    | [], [] -> sm1, sm2, true
    | _, _ -> sm1, sm2, false
  in
  let rec eqt sm1 sm2 t1 t2 =
    match t1, t2 with
    | Var (x1, srt1), Var (x2, srt2) when srt1 = srt2 ->
        let sm1, sm2, b = 
        (try
          sm1, sm2, IdMap.find x1 sm1 = x2
        with Not_found ->
          if IdMap.mem x2 sm2
          then sm1, sm2, false
          else IdMap.add x1 x2 sm1, IdMap.add x2 x1 sm2, true)
        in
        sm1, sm2, b         
    | App (sym1, ts1, srt1), App (sym2, ts2, srt2)
      when sym1 = sym2 && srt1 = srt2 ->
        forall2 eqt sm1 sm2 ts1 ts2
    | _ -> sm1, sm2, false
  in
  let same_capture vs1 vs2 sm1 =
    List.for_all (fun (v1, _) ->
      not (IdMap.mem v1 sm1) ||
      List.mem_assoc (IdMap.find v1 sm1) vs2)
      vs1
  in
  let rec eq sm1 sm2 f1 f2 =
    match f1, f2 with
    | BoolOp (op1, fs1), BoolOp (op2, fs2) when op1 = op2 ->
        forall2 eq sm1 sm2 fs1 fs2
    | Binder (b1, vs1, f1, _), Binder (b2, vs2, f2, _)
      when b1 = b2 && same_capture vs1 vs2 sm1 && same_capture vs2 vs1 sm2 ->
        let remove_bindings sm1 sm2 vs1 =
          List.fold_left 
            (fun (sm1b, sm2b) (v1, _) ->
              if IdMap.mem v1 sm1b then
                let v2 = IdMap.find v1 sm1b in
                IdMap.remove v1 sm1b,
                IdMap.remove v2 sm2b
              else sm1b, sm2b)
            (sm1, sm2) vs1
        in
        let sm1b, sm2b = remove_bindings sm1 sm2 vs1 in
        let sm1b, sm2b, b = eq sm1b sm2b f1 f2 in
        let merge_bindings vs sm smb =
          IdMap.merge (fun v a b ->
            match a, b with
            | a, _ when List.mem_assoc v vs -> a
            | _, b when not (List.mem_assoc v vs) -> b                
            | _ -> None)
            sm smb
        in
        merge_bindings vs1 sm1 sm1b,
        merge_bindings vs2 sm2 sm2b,
        b && same_capture vs1 vs2 sm1b && same_capture vs2 vs1 sm2b
    | Atom (t1, _), Atom (t2, _) ->
        eqt sm1 sm2 t1 t2
    | _ -> sm1, sm2, false
  in
  let sm1, _, b = eq IdMap.empty IdMap.empty f1 f2 in
  (* formulas are structurally equal and all free variables are matched *)
  b && IdMap.for_all (fun x y -> x == y) sm1
    
module FormSet = Set.Make(struct
    type t = form
    let compare f1 f2 =
      if equal f1 f2 then 0 else compare f1 f2
  end)
      
(** {6 List to set conversion functions} *)

let form_set_of_list fs =
  List.fold_left 
    (fun acc f -> FormSet.add f acc) 
    FormSet.empty fs

let term_set_of_list ts =
  List.fold_left 
    (fun acc t -> TermSet.add t acc) 
    TermSet.empty ts

let id_set_of_list ids =
  List.fold_left 
    (fun acc id -> IdSet.add id acc) 
    IdSet.empty ids

(** {6 Utility functions for identifiers, Boolean operators, and sorts} *)

let is_free_symbol = function
  | FreeSym _ -> true
  | _ -> false
    
let fresh_ident =
  let used_names = Hashtbl.create 0 in
  fun  ?(id=0) (name : string) ->
    let last_index = 
      Hashtbl.find_opt used_names name |>
      Opt.get_or_else (-1)
    in
    let new_max = max (last_index + 1) id in
    Hashtbl.replace used_names name new_max;
    (name, new_max)

let dualize_op op = 
  match op with
  | And -> Or
  | Or -> And
  | Not -> failwith "tried to dualize Not"
  
let dualize_binder = function
  | Forall -> Exists
  | Exists -> Forall

let name id = fst id

let range_sort = function
  | Map (_, srt) -> srt
  | _ -> raise (Invalid_argument "range_sort")

let dom_sort = function
  | Map (srt, _) -> srt
  | _ -> raise (Invalid_argument "dom_sort")

let struct_sort_of_sort = function
  | Loc sid -> sid
  | _ -> raise (Invalid_argument "struct_sort_of_sort")

let struct_sort_of_term t =
  struct_sort_of_sort (sort_of t)
        
let range_sort_of_map map =
  match sort_of map with
  | Map (_, srt) -> srt
  | _ -> failwith "illtyped map expression"

let dom_sort_of_map map =
  match sort_of map with
  | Map (srt, _) -> srt
  | _ -> failwith "illtyped map expression"
        
let element_sort_of_sort = function
  | Set srt -> srt
  | _ -> raise (Invalid_argument "element_of_sort")

let element_sort_of_set s =
  match sort_of s with
  | Set srt -> srt
  | _ -> failwith "illtyped set expression"

let element_sort_of_array s =
  match sort_of s with
  | Loc (Array srt) -> srt
  | _ -> failwith "illtyped array expression"

let element_sort_of_cell s =
  match sort_of s with
  | Loc (ArrayCell srt) -> srt
  | _ -> failwith "illtyped array cell expression"

       
let has_sort srt t = sort_of t = srt

let is_set_sort = function
  | Set _ -> true
  | _ -> false

let is_loc_sort = function
  | Loc _ -> true
  | _ -> false

let is_map_sort = function
  | Map _ -> true
  | _ -> false
    
let field_sort id ran_srt = Map ([Loc id], ran_srt)
let array_sort ran_srt = Map ([Int], ran_srt)

let loc_field_sort srt = field_sort srt (Loc srt)

let is_free_const = function
  | App (FreeSym _, [], _) -> true
  | _ -> false

let eq_name id1 id2 = name id1 = name id2

let symbol_of_ident =
  let symbol_map = List.map (fun sym -> (string_of_symbol sym, sym)) symbols in
  fun ((name, _) as id) ->
    List.assoc_opt name symbol_map |>
    Opt.get_or_else (FreeSym id)
 

(** {6 (Smart) constructors} *)

let mk_loc_var name = 
  let id = fresh_ident name in
  fun struct_srt -> id, Loc struct_srt

let mk_loc_field_var name =
  let id = fresh_ident name in
  fun struct_srt -> id, loc_field_sort struct_srt

let mk_loc_set_var name =
  let id = fresh_ident name in
  fun struct_srt -> id, Set (Loc struct_srt)
      
let mk_true = BoolOp (And, [])
let mk_false = BoolOp (Or, [])
let mk_bool b = if b then mk_true else mk_false

let mk_bool_term b = App (BoolConst b, [], Bool)
let mk_true_term = mk_bool_term true
let mk_false_term = mk_bool_term false

let mk_int i = App (IntConst (Int64.of_int i), [], Int)
let mk_int64 i = App (IntConst i, [], Int)

let mk_ident name = (name, 0)

let mk_free_fun srt id args = App (FreeSym id, args, srt)
let mk_free_const srt id = App (FreeSym id, [], srt)
let mk_const srt sym = App (sym, [], srt)

let mk_fresh_var srt name = Var (fresh_ident ("?" ^ name), srt)

let mk_var srt id =  Var (id, srt)

let mk_free_app srt id ts = App (FreeSym id, ts, srt)

let mk_app srt sym ts = App (sym, ts, srt)

let mk_atom ?(ann=[]) sym ts = Atom (mk_app Bool sym ts, ann)

let mk_pred ?(ann=[]) id ts = mk_atom ~ann:ann (FreeSym id) ts

let mk_eq_term s t =
  mk_app Bool Eq [s; t]

let mk_eq ?(ann=[]) s t = mk_atom ~ann:ann Eq [s; t]

let mk_lt_term s t = mk_app Bool Lt [s; t]
let mk_gt_term s t = mk_app Bool Gt [s; t]
let mk_leq_term s t = mk_app Bool LtEq [s; t]
let mk_geq_term s t = mk_app Bool GtEq [s; t]

let mk_lt s t = mk_atom Lt [s; t]
let mk_gt s t = mk_atom Gt [s; t]
let mk_leq s t = mk_atom LtEq [s; t]
let mk_geq s t = mk_atom GtEq [s; t]

let mk_plus s t = mk_app (sort_of s) Plus [s; t]
let mk_minus s t = mk_app (sort_of s) Minus [s; t]
let mk_uminus s = mk_app (sort_of s) UMinus [s]
let mk_mult s t = mk_app (sort_of s) Mult [s; t]
let mk_div s t = mk_app (sort_of s) Div [s; t]
let mk_mod s t = mk_app (sort_of s) Mod [s; t]
let mk_bv_and s t = mk_app (sort_of s) BitAnd [s; t]
let mk_bv_or s t = mk_app (sort_of s) BitOr [s; t]
let mk_bv_not s = mk_app (sort_of s) BitNot [s]
let mk_bv_shift_left s t = mk_app (sort_of s) ShiftLeft [s; t]
let mk_bv_shift_right s t = mk_app (sort_of s) ShiftRight [s; t]
let mk_int_to_byte s = mk_app Byte IntToByte [s]
let mk_byte_to_int s = mk_app Int ByteToInt [s]

let mk_ite c t e = mk_app (sort_of t) Ite [c; t; e]

let mk_null id = mk_app (Loc id) Null []

let mk_read map = function
  | [] -> map
  | inds ->
      let dom_srts, ran_srt = match sort_of map with
      | Map (ds,r) -> ds, r
      | Loc (Array r) -> [Int], r
      | s -> 
          failwith 
	    ("tried to read from term " ^ 
             (string_of_term map) ^ " which is of sort " ^ (string_of_sort s) ^ ".\n" ^
             "Expected sort (Map X Y) for some sorts X, Y.")
      in 
      mk_app ran_srt Read (map :: inds)

let mk_read_form map ind = 
  match sort_of map with
  | Map (_, Bool)
  | Loc (Array Bool) -> mk_atom Read [map; ind]
  | _ -> failwith "mk_read_form expects a term of sort Map(_,Bool)"

let mk_length map =
  mk_app Int Length [map]

let mk_array_map arr =
  mk_app (Map ([Int], element_sort_of_array arr)) ArrayMap [arr]

let mk_array_of_cell c =
  mk_app (Loc (Array (element_sort_of_cell c))) ArrayOfCell [c]

let mk_index_of_cell c =
  mk_app Int IndexOfCell [c]

let mk_array_cells a =
  mk_app (Map ([Int], Loc (ArrayCell (element_sort_of_array a)))) ArrayCells [a]
    
let mk_write map inds upd =
  mk_app (sort_of map) Write (map :: inds @ [upd])

(** Constructor for equalities.*)
let mk_ep fld set t = mk_app (element_sort_of_set set) EntPnt [fld; set; t]

(** Term constructor for between predicates.*)
let mk_btwn_term fld t1 t2 t3 =
  mk_app Bool Btwn [fld; t1; t2; t3]

(** Constructor for between predicates.*)
let mk_btwn ?(ann=[]) fld t1 t2 t3 =
  mk_atom ~ann:ann Btwn [fld; t1; t2; t3]

(** Constructor for reachability predicates.*)
let mk_reach fld t1 t2 = 
  mk_btwn fld t1 t2 t2

(** Constructor for empty set of sort [srt].*)
let mk_empty srt = mk_app srt Empty []

(** Construcot for set constant [id] with elements of sort [Loc srt].*) 
let mk_loc_set srt id = mk_free_const (Set (Loc srt)) id

(** Constructor for set enumerations.*)
let mk_setenum ts = 
  let srt = Set (sort_ofs ts) in
  match ts with
  | [] -> mk_empty srt
  | _ -> mk_app srt SetEnum ts

(** Constructor for set intersection.*)
let mk_inter sets = 
  if List.exists (function App (Empty, [], _) -> true | _ -> false) sets
  then mk_empty (sort_ofs sets)
  else
    let rec mi = function
      | [] -> mk_app (sort_ofs sets) Inter []
      | [s] -> s
      | s1 :: sets ->
          let s2 = mi sets in
          mk_app (sort_of s1) Inter [s1; s2]
    in
    mi sets

(** Constructor for set union.*)
let mk_union sets = 
  let sets1 =
    List.filter 
      (function App (Empty, [], _) -> false | _ -> true) 
      sets
  in
  let rec mu = function
  | [] -> mk_empty (sort_ofs sets)
  | [s] -> s
  | s1 :: sets ->
      let s2 = mu sets in
      mk_app (sort_of s1) Union [s1; s2]
  in
  mu sets1
    
(** Construtor for set difference.*)
let mk_diff s t = mk_app (sort_of s) Diff [s; t]

(** Term constructor for set membership.*)
let mk_elem_term e s = mk_app Bool Elem [e; s]

(** Constructor for set membership.*)
let mk_elem ?(ann=[]) e s = mk_atom ~ann:ann Elem [e; s]

(** Smart constructor for set membership.*)
let smk_elem ?(ann=[]) e = function
  | App (Empty, _, _) -> mk_false
  | s -> mk_elem ~ann:ann e s

(** Constructor for subset constraints.*)
let mk_subseteq_term s t = mk_app Bool SubsetEq [s; t]
let mk_subseteq s t = mk_atom SubsetEq [s; t]

(** Term constructor for disjointness constraints.*)
let mk_disjoint_term s t = mk_app Bool Disjoint [s; t]

(** Constructor for disjointness constraints.*)
let mk_disjoint s t =
    if s = t
    then mk_false
    else mk_atom Disjoint [s; t]

(** Term constructor for frame predicates.*)
let mk_frame_term x a f f' = mk_app Bool Frame [x; a; f; f']

(** Constructor for frame predicates.*)
let mk_frame x a f f' = mk_atom Frame [x; a; f; f']

(** Constructor for disjunction.*)
let mk_and = function
  | [f] -> f
  | fs -> BoolOp(And, fs)

(** Constructor for conjunction.*)
let mk_or = function
  | [f] -> f
  | fs -> BoolOp (Or, fs)

(** Constructor for negation.*)
let mk_not = function
  | BoolOp (op, []) -> BoolOp (dualize_op op, [])
  | BoolOp (Not, [f]) -> f
  | f -> BoolOp (Not, [f])

(** Constructor for disequality.*)
let mk_neq s t = mk_not (mk_eq s t)

(** Constructor for strict subset constraints.*)
let mk_strict_subset s t = mk_and [mk_subseteq s t; mk_neq s t]

(** Constructor for oldification *)
let mk_old t = mk_app (sort_of t) Old [t]
    
(** Constructor for patterns. *)
let mk_known t = mk_app Pat Known [t]

(** Constructor for ADT destructor terms. *)
let mk_constr srt constr ts = mk_app srt (Constructor constr) ts

(** Constructor for ADT destructor terms. *)
let mk_destr srt destr t = mk_app srt (Destructor destr) [t]
    
(** Constructor for binder [b], binding variables [bv] in formula [f]. 
 *  Annotations [ann] are optional.
 *)
let rec mk_binder ?(ann=[]) b bv f = 
  match bv, ann with 
  | [], [] -> f
  | _ -> 
      match f with
      | Binder (_, [], f', ann') ->
          mk_binder ~ann:(ann @ ann') b bv f'
      | Binder (b', bv', f', ann') when b = b' ->
          mk_binder ~ann:(ann @ ann') b (bv @ bv') f'
      | BoolOp (op, []) -> f
      | _ -> Binder (b, bv, f, ann)

(** Constructor for universal quantification.*)
let mk_forall ?(ann=[]) bv f = mk_binder ~ann:ann Forall bv f

(** Constructor for existential quantification.*)
let mk_exists ?(ann=[]) bv f = mk_binder ~ann:ann Exists bv f 
  
(** Add anntotations [ann] to formula [f]. *)
let annotate f ann =
  let gen = List.filter (function TermGenerator _ -> true | _ -> false) ann in
  match f, gen with
  | Atom (t, ann1), [] -> Atom (t, ann @ ann1)
  | Binder (b, vs, f1, ann1), [] -> Binder (b, vs, f1, ann @ ann1)
  | Binder (b, [], f1, ann1), _ -> Binder (b, [], f1, ann @ ann1)
  | _, _ -> 
      match ann with
      | [] -> f
      | _ -> Binder (Forall, [], f, ann)

(** Filter all annotations in formula [f] according to filter [fn]. *)
let filter_annotations fn f = 
  let rec fa = function
    | BoolOp (op, fs) ->
        BoolOp (op, List.map fa fs)
    | Atom (t, ann) ->
        Atom (t, List.filter fn ann)
    | Binder (b, vs, f, ann) ->
        let f1 = fa f in
        Binder (b, vs, f1, List.filter fn ann)
  in fa f

(** Remove all annotations from formula [f]. *)
let strip_annotations f =
  filter_annotations (fun _ -> false) f
    
(** Remove all comments from formula [f]. *)
let strip_comments f = 
  filter_annotations 
    (function Comment _ -> false | _ -> true) f

(** Remove all error messages from formula [f]. *)
let strip_error_msgs f = 
  filter_annotations 
    (function ErrorMsg _ -> false | _ -> true) f

(** Remove all name annotations from formula [f]. *)
let strip_names f = 
  filter_annotations 
    (function Name _ -> false | _ -> true) f

(** Extract patterns from formula [f].*)
let extract_patterns f =
  let extract acc ann =
    List.fold_left
      (fun acc -> function Pattern (t, fs) -> (t, fs) :: acc | _ -> acc)
      acc ann
  in
  let rec ep acc = function
    | BoolOp (op, fs) ->
        List.fold_left ep acc fs
    | Atom (_, ann) ->
        extract acc ann
    | Binder (_, _, f, ann) ->
        ep (extract acc ann) f
  in ep [] f
  
(** Annotate [f] with comment [c]. *)
let mk_comment c f = 
  annotate f [Comment c]

(** Annotate [f] with error message [msg] associated with position [pos]. *)
let mk_error_msg (pos, msg) f =
  annotate f [ErrorMsg (pos, msg)]

(** Annotate [f] with name [n]. *)
let mk_name n f = annotate f [Name (fresh_ident n)]

(** Annotate [f] with source position [pos].*)
let mk_srcpos pos f = annotate f [SrcPos pos]

(** Annotate [f] with pattern [t] and filter [ft]. *)
let mk_pattern t ft f = annotate f [Pattern (mk_known t, ft)]

   
(** Smart constructor for Boolean operation [op] taking arguments [fs].*)
let smk_op op fs =
  match op with
  | Not -> mk_not (List.hd fs)
  | _ ->
      let collect acc =
        function
          | BoolOp (And, gs)
          | Binder (_, [], (BoolOp (And, gs)), _) ->
            let gss =
              List.fold_left (fun gss g -> FormSet.add g gss) FormSet.empty gs
            in
            acc |> Opt.map (FormSet.inter gss) |> Opt.some gss
          | f ->
              let gss = FormSet.singleton f in
              acc |> Opt.map (FormSet.inter gss) |> Opt.some gss
      in
      let filter common f fs =
        match f with
        | BoolOp (And, gs) ->
            let gs1 =
              List.filter (fun g -> not @@ FormSet.mem g common) gs
            in
            mk_and gs1 :: fs
        | Binder (_, [], BoolOp (And, gs), a) ->
            let gs1 =
              List.filter (fun g -> not @@ FormSet.mem g common) gs
            in
            annotate (mk_and gs1) a :: fs
        | f -> f :: fs 
      in
      let distr fs =
        match fs with
        | [f] -> f
        | _ :: _ when op = Or ->
            let common = List.fold_left collect None fs |> Opt.get in
            let fs1 = List.fold_right (filter common) fs [] in
            mk_and (mk_or fs1 :: FormSet.elements common)
        | _ -> BoolOp (op, fs)
      in
      let rec mkop1 fs acc = 
	match fs with
	| [] -> distr (FormSet.elements acc)
	| BoolOp (op', fs0) :: fs1 when op = op' -> 
	    mkop1 (fs0 @ fs1) acc
	| BoolOp (And, []) :: fs1
        | Atom (App (BoolConst true, [], _), _) :: fs1 when op = Or -> mk_true
	| BoolOp (Or, []) :: fs1
        | Atom (App (BoolConst false, [], _), _) :: fs1 when op = And -> mk_false
	| f :: fs1 ->
            if FormSet.mem (mk_not f) acc then BoolOp (dualize_op op, [])
            else mkop1 fs1 (FormSet.add f acc)
      in mkop1 fs FormSet.empty

(** Smart constructor for conjunctions. *)
let smk_and fs = smk_op And fs

(** Smart constructor for disjunctions. *)
let smk_or fs = smk_op Or fs

let smk_disjoint s t =
  match s, t with
  | App (Empty, _, _), _
  | _, App (Empty, _, _) -> mk_true
  | _ -> mk_disjoint s t
    
(** {6 Normal form computation} *)

(** Compute negation normal form of a formula *)
let rec nnf = function
  | BoolOp (Not, [BoolOp (Not, [f])]) -> nnf f
  | BoolOp (Not, [BoolOp (op, fs)]) -> 
      smk_op (dualize_op op) (List.map (fun f -> nnf (mk_not f)) fs)
  | BoolOp (Not, [Binder (b, [], f, a)]) ->
      mk_binder ~ann:a b [] (nnf (mk_not f))
  | BoolOp (Not, [Binder (b, vs, f, a)]) -> 
      mk_binder ~ann:a (dualize_binder b) vs (nnf (mk_not f))
  | BoolOp (Not, [Atom (App (BoolConst b, [], _), _)]) ->
      mk_bool (not b)
  | BoolOp (op, fs) -> smk_op op (List.map nnf fs)
  | Binder (b, vs, f, a) -> mk_binder ~ann:a b vs (nnf f)
  | f -> f
  
(** Compute conjunctive normal form of a formula *)
(* Todo: avoid exponential blow-up *)
let rec cnf = 
  let rec cnf_and acc = function
    | [] -> mk_and acc
    | BoolOp (Or, []) :: _ -> BoolOp (Or, [])
    | BoolOp (And, fs) :: fs1 -> cnf_and acc (fs @ fs1)
    | f :: fs -> cnf_and (f :: acc) fs
  in
  let rec cnf_or acc = function
    | BoolOp (And, []) :: _ -> BoolOp (And, [])
    | [] -> mk_or acc
    | BoolOp(Or, fs) :: fs1 -> cnf_or acc (fs @ fs1)
    | BoolOp (And, fs) :: fs1 -> 
	let fs_or = acc @ fs1 in
	let fs_and = List.map (fun f -> mk_or (f :: fs_or)) fs in
	cnf (mk_and fs_and)
    | f :: fs -> cnf_or (f :: acc) fs  
  in
  function
    | BoolOp(And, fs) -> cnf_and [] (List.rev_map cnf fs)
    | BoolOp (Or, fs) -> cnf_or [] (List.rev_map cnf fs)
    | f -> f

(** Compute disjunctive normal form of a formula *)
(* Todo: avoid exponential blow-up *)
let rec dnf = 
  let rec dnf_or acc = function
    | [] -> mk_or acc
    | BoolOp (And, []) :: _ -> BoolOp (And, [])
    | BoolOp (Or, fs) :: fs1 -> dnf_or acc (fs @ fs1)
    (* Pass through empty binders *)
    | Binder (_, [], f, _) :: fs1 -> dnf_or acc (f :: fs1)
    | f :: fs -> dnf_or (f :: acc) fs
  in
  let rec dnf_and acc = function
    | BoolOp (Or, []) :: _ -> BoolOp (Or, [])
    | [] -> mk_and acc
    | BoolOp(And, fs) :: fs1 -> dnf_and acc (fs @ fs1)
    | BoolOp (Or, fs) :: fs1 -> 
      let fs_and = acc @ fs1 in
      let fs_or = List.map (fun f -> mk_and (f :: fs_and)) fs in
      dnf (mk_or fs_or)
    (* Pass through empty binders *)
    | Binder (_, [], f, _) :: fs1 -> dnf_and acc (f :: fs1)
    | f :: fs -> dnf_and (f :: acc) fs  
  in
  function
    | BoolOp(Or, fs) -> dnf_or [] (List.rev_map dnf fs)
    | BoolOp (And, fs) -> dnf_and [] (List.rev_map dnf fs)
    | f -> f

(** Construtor for implications. *)
let mk_implies f g =
  match g with
  | Binder (b, [], g1, a) ->
      Binder (b, [] , smk_or [nnf (mk_not f); g1], a)
  | _ -> smk_or [nnf (mk_not f); g]

(** Constructor for sequents.*)
let mk_sequent antecedent succedent =
  smk_or (List.map mk_not antecedent @ succedent)

(** Constructor for biimplication.*)
let mk_iff a b =
  smk_or [smk_and [a; b]; smk_and [nnf (mk_not a); nnf (mk_not b)]]


(** {6 Generic term and formula manipulation, substitution functions} *)

(** Orient terms *)
let orient_terms t1 t2 = if compare t1 t2 < 0 then (t1, t2) else (t2, t1)
    
(** Check whether term [t] is ground *)

let rec is_ground_term = function
  | Var _ -> false
  | App (_, ts, _) -> List.for_all is_ground_term ts

(** Check whether formula [f] is ground *)
let is_ground =
  let rec gf = function
   | Binder (_, [], f, _) -> gf f
   | Binder (_, _, _, _) -> false
   | BoolOp (_, fs) -> List.for_all gf fs
   | Atom (t, an) -> is_ground_term t
  in gf
    
(** Fold all terms appearing in the formula [f] using catamorphism [fn] and initial value [init] *)
let fold_terms fn init f =
  let fa acc = function
    | Pattern (t, _) -> fn acc t
    | Label (_, t) -> fn acc t
    | TermGenerator (ms, ts) ->
        let acc1 =
          List.fold_left
            (fun acc -> function Match (t, _) -> fn acc t)
            acc ms
        in
        List.fold_left fn acc1 ts
    | _ -> acc
  in
  let rec ft acc = function
    | Atom (t, a) -> fn (List.fold_left fa acc a) t
    | BoolOp (_, fs) ->	List.fold_left ft acc fs
    | Binder (_, _, f, a) ->
        ft (List.fold_left fa acc a) f
  in ft init f

(** Apply the function fn to all terms appearing in [f] *)
let map_terms fn f =
  let ma a =
     List.map (function
       | TermGenerator (gs, ts) ->
           let gs1 = List.map (function Match (t, f) -> Match (fn t, f)) gs in
           TermGenerator (gs1, List.map fn ts)
       | Pattern (t, ft) -> Pattern (fn t, ft)
       | Label (pol, t) -> Label (pol, fn t)
       | a -> a) a
  in
  let rec mt = function
    | Atom (t, a) -> Atom (fn t, ma a)
    | BoolOp (op, fs) -> BoolOp (op, List.map mt fs)
    | Binder (b, vs, f, a) -> Binder (b, vs, mt f, ma a)
  in mt f

(** Fold and map all terms appearing in the formula [f]
  using [fn] and initial value [init] *)
let fold_map_terms fn init f =
  let fa acc = function
    | Pattern (t, fs) ->
      let t, acc = fn acc t in
      Pattern(t, fs), acc
    | Label (b, t) -> let t, acc = fn acc t in Label (b, t), acc
    | TermGenerator (gs, ts) ->
      let gs, acc =  (* TODO should we also apply it to terms in filters? *)
        fold_left_map (fun acc -> function Match (t, fs) ->
          let t, acc = fn acc t in Match (t, fs), acc) acc gs
      in
      let ts, acc = fold_left_map fn acc ts in
      TermGenerator (gs, ts), acc
    | Comment _ | SrcPos _ | Name _ | ErrorMsg _ as a -> a, acc
  in
  let rec ft acc = function
    | Atom (t, a) ->
      let a, acc = fold_left_map fa acc a in
      let t, acc = fn acc t in
      Atom (t, a), acc
    | BoolOp (op, fs) ->
      let fs, acc = fold_left_map ft acc fs in
      BoolOp (op, fs), acc
    | Binder (b, vs, f, a) ->
      let a, acc = fold_left_map fa acc a in
      let f, acc = ft acc f in
      Binder (b, vs, f, a), acc
  in ft init f

(** Apply the function fn to all atoms appearing in [f] *)
let map_atoms fn f =
  let rec mt = function
    | Atom (t, a) -> annotate (fn t) a
    | BoolOp (Not, [Atom (t, a)]) ->
        (match annotate (fn t) a with
        | BoolOp (Not, [f]) -> f
        | f1 -> BoolOp (Not, [f1]))
    | BoolOp (op, fs) -> BoolOp (op, List.map mt fs)
    | Binder (b, vs, f, a) -> Binder (b, vs, mt f, a)
  in mt f

(** Like {!fold_terms} except that [fn] takes the set of bound variables of the given context as additional argument *)
let fold_terms_with_bound fn init f =
  let fa bv acc = function
    | Pattern (t, _) -> fn bv acc t
    | Label (_, t) -> fn bv acc t
    | _ -> acc
  in
  let rec ft bv acc = function
    | Atom (t, a) -> fn bv (List.fold_left (fa bv) acc a) t
    | BoolOp (_, fs) ->	List.fold_left (ft bv) acc fs
    | Binder (_, vs, f, a) ->
        let bv1 = List.fold_left (fun bv (x, _) -> IdSet.add x bv) bv vs in
        ft bv1 (List.fold_left (fa bv1) acc a) f
  in ft IdSet.empty init f
    
(** Computes the set of identifiers of free variables occuring in term [t]
 ** union the accumulated set of identifiers [vars]. *)
let fv_term_acc vars t =
  let rec fvt1 vars = function
  | Var (id, _) -> IdSet.add id vars
  | App (_, ts, _) -> List.fold_left fvt1 vars ts
  in fvt1 vars t

(** Computes the set of free variables occuring in term [t]. *)
let fv_term t = fv_term_acc IdSet.empty t

(** Computes the set of free variables occuring in formula [f]. *)
let fv f = 
  let rec fvt bv vars = function
    | Var (id, _) -> 
	if IdSet.mem id bv 
	then vars 
	else IdSet.add id vars
    | App (_, ts, _) ->
	List.fold_left (fvt bv) vars ts
  in fold_terms_with_bound fvt IdSet.empty f

(** Computes the signature of free variables occuring in term [t]
 ** union the accumulated variable signature [svars]. *)
let sorted_fv_term_acc svars t =
  let rec fvt1 svars = function
  | Var (id, srt) -> IdMap.add id srt svars
  | App (_, ts, _) -> List.fold_left fvt1 svars ts
  in fvt1 svars t

(** Smart constructor for binder [b], binding variables [bv] in formula [f]. *)
let smk_binder ?(ann=[]) b bv f =
  let fv_f = fv (annotate f ann) in
  let bv1 = List.filter (fun (x, _) -> IdSet.mem x fv_f) bv in
  mk_binder ~ann:ann b bv1 f

(** Smart constructor for universal quantifiers.*)
let smk_forall ?(ann=[]) bv f = smk_binder ~ann:ann Forall bv f

(** Smart constructor for existential quantifiers.*)
let smk_exists ?(ann=[]) bv f = smk_binder ~ann:ann Exists bv f

(** Computes the size of the term [t] (in number of function applications) *)
let size_of_term t =
  let rec s acc = function
  | Var _ -> acc
  | App (_, ts, _) -> List.fold_left s (acc + 1) ts
  in s 0 t
    
(** Computes the set of free variables of formula [f] together with their sorts. *)
let sorted_free_vars f = 
  let rec fvt bv vars = function
    | Var (id, srt) -> 
	if IdSet.mem id bv 
	then vars 
	else IdSrtSet.add (id, srt) vars
    | App (_, ts, _) ->
	List.fold_left (fvt bv) vars ts
  in fold_terms_with_bound fvt IdSrtSet.empty f

(** Computes the set of all sorts of the terms appearing in formula [f]. *)
let sorts f =
  let rec s acc = function
    | Var (_, srt) -> SortSet.add srt acc
    | App (_, ts, srt) ->
        let acc1 = SortSet.add srt acc in
        List.fold_left s acc1 ts
  in
  fold_terms s SortSet.empty f

(** Unfold the sort variables standing for ADTs [adts] in sort [srt] *)
let unfold_adts adts srt =
  let rec unfold srt = match srt with
  | FreeSrt sid ->
    List.assoc_opt sid adts |>
    Util.Opt.map (fun _ -> Adt (sid, adts)) |>
    Util.Opt.get_or_else srt
  | Map (asrts, rsrt) -> Map (List.map unfold asrts, unfold rsrt)
  | Set ssrt -> Set (unfold ssrt)
  | Loc lsrt -> Loc (unfold lsrt)
  | Array asrt -> Array (unfold asrt)
  | ArrayCell asrt -> ArrayCell asrt
  | _ -> srt
  in 
  unfold srt
    
(** Computes the set of free constants occuring in term [t].
 ** Takes accumulator [consts] as additional argument. *)
let free_consts_term_acc consts t =
  let rec fct consts = function
  | Var _ -> consts
  | App (FreeSym id, [], _) -> IdSet.add id consts
  | App (_, ts, _) -> List.fold_left fct consts ts
  in fct consts t

(** Computes the set of free constants occuring in term [t]. *)
let free_consts_term t = free_consts_term_acc IdSet.empty t

(** Computes the set of free constants occuring in formula [f].
 ** Takes accumulator [consts] as additional argument. *)
let free_consts_acc consts f = fold_terms free_consts_term_acc consts f

(** Computes the set of free constants occuring in formula [f]. *)
let free_consts f =
  fold_terms free_consts_term_acc IdSet.empty f
    
(** Computes the set of free symbols occuring in term [t].
 ** Takes accumulator [acc] as additional argument. *)
let free_symbols_term_acc acc t =
  let rec fst acc = function
    | Var _ -> acc
    | App (sym, ts, _) -> 
        let acc1 = match sym with
        | FreeSym id -> IdSet.add id acc
        | _ -> acc
        in
        List.fold_left fst acc1 ts
  in fst acc t

(** Computes the set of free symbols occuring in term [t]. *)
let free_symbols_term t = free_symbols_term_acc IdSet.empty t

(** Computes the set of free symbols occuring in formula [f]. *)
let free_symbols f =
  fold_terms free_symbols_term_acc IdSet.empty f

(** Computes the set of subterms of a term [t].
 ** Takes accumulator [terms] as additional arguments *)
let subterms_term_acc terms t =
  let rec st terms t =
    let terms1 = TermSet.add t terms in
    match t with
    | App (_, ts, _) ->
	List.fold_left st terms1 ts
    | _ -> terms1
  in
  st terms t
  
    
(** Computes the set of all ground terms in term [t].
 ** Takes accumulator [terms] as additional arguments *)
let ground_terms_term_acc ?(include_atoms=false) terms t =
  let rec gt terms t = 
    match t with
    | Var (id, _) -> terms, false
    | App (_, ts, srt) ->
	let terms1, is_ground = 
	  List.fold_left 
	    (fun (terms, is_ground) t ->
	      let terms_t, is_ground_t = gt terms t in
	      terms_t, is_ground && is_ground_t)
	    (terms, true) ts
	in
	if is_ground && (include_atoms || srt <> Bool)
	then TermSet.add t terms1, true 
	else terms1, is_ground
  in
  fst (gt terms t)

(** Computes the set of all ground terms in term [t]. *)
let ground_terms_term ?(include_atoms=false) t =
  ground_terms_term_acc ~include_atoms:include_atoms TermSet.empty t

(** Computes the set of ground terms appearing in [f].
 ** Free variables are treated as implicitly universally quantified.
 ** Takes accumulator [terms] as additional argument. *)
let ground_terms_acc ?(include_atoms=false) terms f =
   fold_terms
    (ground_terms_term_acc ~include_atoms:include_atoms) 
    terms f
    
(** Computes the set of ground terms appearing in [f].
 ** Free variables are treated as implicitly universally quantified *)
let ground_terms ?(include_atoms=false) f =
   fold_terms
    (ground_terms_term_acc ~include_atoms:include_atoms) 
    TermSet.empty f
  
(** Computes the set of all free variables that appear below function symbols in formula [f]. *)
let vars_in_fun_terms f =
  let rec fvt vars = function
    | Var (id, srt) ->
        IdSrtSet.add (id, srt) vars
    | App (_, ts, _) ->
	List.fold_left fvt vars ts
  in
  let rec ct vars t = 
    match t with
    | App (_, ts, Bool) | App (Known, ts, _) -> 
	List.fold_left ct vars ts
    | App _ -> fvt vars t
    | _ -> vars
  in fold_terms ct IdSrtSet.empty f

let terms_with_vars f =
  let rec process acc t = match t with
    | App (sym, ts, srt) ->
      let acc = List.fold_left process acc ts in
      if not (IdSet.is_empty (fv_term_acc IdSet.empty t))
      then TermSet.add t acc
      else acc
    | Var _ -> acc
  in
  fold_terms process TermSet.empty f
    
    
(** Compute the set of all proper terms in formula [f] that have variables occuring in them. *)
let fun_terms_with_vars f =
  let rec process acc t = match t with
    | App (sym, ts, srt) when srt <> Bool ->
      let acc = List.fold_left process acc ts in
      if not (IdSet.is_empty (fv_term_acc IdSet.empty t))
      then TermSet.add t acc
      else acc
    | App (_, ts, _) ->
      (* skip predicates *)
      List.fold_left process acc ts
    | Var _ -> acc
  in
  fold_terms process TermSet.empty f
     
(** Extract signature of term [t] with accummulator. *)
let rec sign_term_acc (decls : signature) t = 
  match t with
  | Var _ -> decls
  | App (sym, args, res_srt) ->
      let arg_srts = 
        List.map
	  (function 
	    | Var (_, srt) 
	    | App (_, _, srt) -> srt 
	  )
	  args
      in List.fold_left sign_term_acc (SymbolMap.add sym (arg_srts, res_srt) decls) args

(** Extract signature of term [t]. *)
let sign_term t = sign_term_acc SymbolMap.empty t
        
(** Extracts the signature of formula [f]. *)
let sign f : signature =
  fold_terms sign_term_acc SymbolMap.empty f

(** Extracts the signature of formula [f]. *)
let overloaded_sign f : (arity list SymbolMap.t) =
  let add_to_sign sym tpe decls =
    let old = SymbolMap.find_opt sym decls |> Opt.get_or_else [] in
      if List.mem tpe old then decls
      else SymbolMap.add sym (tpe :: old) decls
  in
  let rec signt (decls : arity list SymbolMap.t) t = match t with
    | Var _ -> decls
    | App (sym, args, res_srt) ->
	let arg_srts = List.map sort_of args in
	List.fold_left signt (add_to_sign sym (arg_srts, res_srt) decls) args
  in 
  fold_terms signt SymbolMap.empty f

(** Map all identifiers occuring in term [t] to new identifiers according to function [fct] *)
let map_id_term fct t =
  let rec sub = function
    | Var (id, srt) -> Var (fct id, srt)
    | App (sym, ts, srt) -> 
	let sym1 = match sym with
	| FreeSym id -> FreeSym (fct id)
	| _ -> sym
	in
	App (sym1, List.map sub ts, srt)
  in sub t

(** Map all identifiers occuring in formula [f] to new identifiers according to function [fct] *)
let map_id fct f =
  let mapt = map_id_term fct in
  let mapf f = match f with
    | FilterSymbolNotOccurs (FreeSym id) ->
        (try FilterSymbolNotOccurs (FreeSym (fct id))
        with Not_found -> f)
          (*| FilterTermNotOccurs t ->
             FilterTermNotOccurs (subt t)*)
    | f -> f
  in
  let mapg g = match g with
  | Match (t, fs) ->
      let t1 = mapt t in
      let fs1 = List.map mapf fs in
      Match (t1, fs1)
  in
  let mapa a = match a with
    | TermGenerator (guards, gen_terms) -> 
        TermGenerator (List.map mapg guards, List.map mapt gen_terms)
    | Pattern (t, fs) -> Pattern (mapt t, List.map mapf fs)
    | Label (pol, t) -> Label (pol, mapt t)
    | a -> a
  in
  let rec sub = function 
    | BoolOp (op, fs) -> BoolOp (op, List.map sub fs)
    | Atom (t, a) -> Atom (map_id_term fct t, List.map mapa a)
    | Binder (b, vs, f, a) -> Binder (b, vs, sub f, List.map mapa a)
  in sub f

(** Substitutes all identifiers in term [t] with other identifiers according to substitution map [subst_map] *)
let subst_id_term subst_map t =
  let sub_id id =
    IdMap.find_opt id subst_map |> Opt.get_or_else id
  in
  map_id_term sub_id t

(** Substitutes all identifiers in formula [f] with other identifiers according to substitution map [subst_map].
 ** This operation is not capture avoiding. *)
let subst_id subst_map f =
  let sub_id id =
    IdMap.find_opt id subst_map |> Opt.get_or_else id
  in
  map_id sub_id f

(** Substitutes all constants in term [t] with other terms according to substitution function [subst_fun]. *)
let subst_consts_fun_term subst_fun t =
  let rec sub = function
    | (App (FreeSym id, [], srt) as t) -> 
        subst_fun id t
    | App (sym, ts, srt) -> App (sym, List.map sub ts, srt)
    | t -> t
  in
  sub t

(** Substitutes all constants in formula [f] with other terms according to substitution function [subst_fun]. 
 ** This operation is not capture avoiding. *)
let subst_consts_fun subst_fun f =
  map_terms (subst_consts_fun_term subst_fun) f

(** Substitutes all constants in term [t] with other terms according to substitution map [subst_map]. *)
let subst_consts_term subst_map t =
  let sub_id id t =
    IdMap.find_opt id subst_map |> Opt.get_or_else t
  in
  subst_consts_fun_term sub_id t

(** Substitutes all constants in formula [f] with other terms according to substitution map [subst_map]. 
 ** This operation is not capture avoiding. *)
let subst_consts subst_map f =
  let subst_filter f = match f with
    | FilterSymbolNotOccurs (FreeSym id) ->
        (match IdMap.find_opt id subst_map with
          | Some (App (FreeSym id1, [], _)) ->
              FilterSymbolNotOccurs (FreeSym id1)
          | _ -> f)
    | f -> f
  in
  let subst_annot = function
    | TermGenerator (guards, gen_terms) -> 
        let sign, guards1 = 
          List.fold_right 
            (fun m (sign, guards1) -> 
              match m with
              | Match (t, fs) ->
                  let t1 = subst_consts_term subst_map t in
                  let fs1 = List.map subst_filter fs in
                  sorted_fv_term_acc sign t1, Match (t1, fs1) :: guards1)
            guards (IdMap.empty, [])
        in
        TermGenerator (guards1, List.map (subst_consts_term subst_map) gen_terms)
    | Pattern (t, fs) -> Pattern (subst_consts_term subst_map t, List.map subst_filter fs)
    | Label (pol, t) -> Label (pol, subst_consts_term subst_map t)
    | a -> a
  in
  let rec subst = function
    | BoolOp (op, fs) -> BoolOp (op, List.map subst fs)
    | Atom (t, a) ->
        Atom (subst_consts_term subst_map t, List.map subst_annot a)
    | Binder (b, vs, f, a) ->
        Binder (b, vs, subst f, List.map subst_annot a)
  in
  subst f


(** Substitutes all variables in term [t] with terms according to substitution map [subst_map]. 
 ** This operation is not capture avoiding. *)
let subst_term subst_map t =
  let sub_id id t =
    IdMap.find_opt id subst_map |>
    Opt.get_or_else t
  in
  let rec sub = function
    | Var (id, srt) as t -> sub_id id t 
    | App (sym, ts, srt) as t ->
        let changed, ts1 =
          List.fold_right (fun t (changed, ts1) ->
            let t1 = sub t in
            changed || t != t1, t1 :: ts1) ts (false, [])
        in
        if changed 
        then App (sym, ts1, srt)
        else t
  in sub t

(** Substitute all function applications in term [t] according to function [fct]. *)
let subst_funs_term fct t =
   let rec sub = function
   | App (sym, ts, srt) -> 
       let ts1 = List.map sub ts in
       fct sym ts1 srt
   | Var _ as t -> t
   in
   sub t

(** Substitute all function applications in formula [f] according to function [fct]. 
 ** This operation is not capture avoiding. *)
let subst_funs fct f =
  map_terms (subst_funs_term fct) f

(** Substitutes all free variables in an annotation with terms according to substitution map [subst_map].
 ** This operation is capture avoiding. *)
let subst_annot subst_map = function
    | TermGenerator (guards, gen_terms) -> 
        let guards1 = 
          List.map
            (function Match (t, f) -> Match (subst_term subst_map t, f))
            guards
        in
        let gen_terms1 =
          List.map (subst_term subst_map)
            gen_terms
        in
        TermGenerator (guards1, gen_terms1)
    | Pattern (t, fs) ->
        Pattern (subst_term subst_map t, fs)
    | Label (pol, t) ->
        Label (pol, subst_term subst_map t)
    | a -> a
    
(** Substitutes all free variables in formula [f] with terms according to substitution map [subst_map].
 ** This operation is capture avoiding. *)
let subst subst_map f =
  (** Given a list of bound variables [vs] and a substitution map [sm], discards mappings
    of variables that are bound and renames bound variables that conflict with terms in
    the RHS of substitutions.
  *)
  let rename_vars vs sm =
    let not_bound id _ = not (List.mem_assoc id vs) in
    let sm1 = IdMap.filter not_bound sm in 
    let occuring = IdMap.fold (fun _ t acc -> fv_term_acc acc t) sm IdSet.empty in
    List.fold_right 
      (fun (x, srt) (vs1, sm2) ->
	if IdSet.mem x occuring 
	then 
	  let x1 = fresh_ident (name x) in
	  (x1, srt) :: vs1, IdMap.add x (Var (x1, srt)) sm2
	else (x, srt) :: vs1, sm2)
      vs ([], sm1)
  in
  let rec sub sm = function 
    | BoolOp (op, fs) ->
        let fs1 =
          List.map (sub sm) fs
        in
        BoolOp (op, fs1)
    | Atom (t, aa) ->
        let t1 = subst_term sm t in
        let aa1 = List.map (subst_annot sm) aa in
        Atom (t1, aa1)
    | Binder (b, vs, bf, aa) ->
        let vs1, sm1 = rename_vars vs sm in
        let bf1 = sub sm1 bf in
        let aa1 = List.map (subst_annot sm1) aa in
        Binder (b, vs1, bf1, aa1)
  in sub subst_map f


(** Split top-level conjunctions into conjuncts *) 
let split_ands fs =
  let rec split acc = function
    | BoolOp(And, fs) :: gs -> 
        split acc (fs @ gs)
    | Binder(_, [], BoolOp(And, fs), a) :: gs ->
        split acc (List.map (fun f -> annotate f a) fs @ gs)
    | f :: gs ->
        split (f :: acc) gs
    | [] -> List.rev acc
  in split [] fs
    

(** Propagate [b] quantified variables upward in the formula [f].
 ** Assumes that [f] is in negation normal form. *)
let propagate_binder_up b f =
  let rec merge sm zs xs ys ys2 =
    match xs, ys with
    | (x, srt1) :: xs1, (y, srt2) :: ys1 ->
        if srt1 = srt2
        then merge (IdMap.add x (mk_var srt1 y) sm) ((y, srt2) :: zs) xs1 (ys2 @ ys1) []
        else merge sm zs xs ys1 ((y, srt2) :: ys2)
    | [], _ -> sm, ys @ ys2 @ zs
    | _, [] -> 
        if ys2 = [] then sm, xs @ zs
        else merge sm (List.hd xs :: zs) (List.tl xs) ys2 []
  in
  let rec prop_op_same tvs op fs =
    let fs1, vs = 
      List.fold_right (fun f (fs2, vs2) ->
        let f1, vs1 = prop tvs (mk_binder b tvs f) in
        let sm, vs = merge IdMap.empty [] vs1 vs2 [] in
        subst sm f1 :: fs2, vs) 
        fs ([], [])
    in
    (*if op = Or && List.length fs1 = 2 then begin
      print_endline "propagating";
      print_form stdout (mk_or fs1);
      print_newline ();
    end;*)
    smk_op op fs1, vs
  and prop_op_diff tvs op fs =
    let fv_fs = fv (BoolOp (op, fs)) in
    let fvs, used =
      let rec distribute (fvs, unused, used) = function
        | f :: fs -> 
            let fv_f = fv f in
            let ftvs_set = IdSet.diff (IdSet.inter unused fv_f) (fv (BoolOp (op, fs))) in
                (*print_form stdout f; print_newline();
                   print_endline "vars: ";
                   IdSet.iter (fun id -> Printf.printf "%s, " (string_of_ident id)) ftvs_set; print_newline(); print_newline();*)
            let ftvs = List.filter (fun (x, _) -> IdSet.mem x ftvs_set) tvs in
            distribute ((f, ftvs) :: fvs, IdSet.diff unused fv_f, IdSet.union used ftvs_set) fs
        | [] -> fvs, used
      in 
      let tvs_set = List.fold_left (fun acc (x, _) -> IdSet.add x acc) IdSet.empty tvs in
      distribute ([], tvs_set, IdSet.empty) fs 
    in
    let tvs1 = List.filter (fun (x, _) -> IdSet.mem x fv_fs && not (IdSet.mem x used)) tvs in
    let fs1, vss = List.split (List.map (fun (f, ftvs) -> prop ftvs f) fvs) in
    smk_op op fs1, List.concat (tvs1 :: vss)
  and prop tvs = function
    | BoolOp (And, fs) when b = Forall ->
        prop_op_same tvs And fs
    | BoolOp (Or, fs) when b = Exists ->
        prop_op_same tvs Or fs
    | BoolOp (Or, fs) when b = Forall ->
        prop_op_diff tvs Or fs
    | BoolOp (And, fs) when b = Exists ->
        prop_op_diff tvs And fs
    | Binder (b1, vs, f, a) when b = b1 -> 
        let vars = fv f in
        let vs0 = List.filter (fun (v, _) -> IdSet.mem v vars) vs in
        let sm, vs1 = 
          List.fold_right 
            (fun (v, srt) (sm, vs1) -> 
              let v1 = fresh_ident (name v) in
              IdMap.add v (mk_var srt v1) sm, (v1, srt) :: vs1)
            vs0 (IdMap.empty, tvs)
        in
        let f1, vs2 = prop vs1 (subst sm f) in
        (match a with 
        | [] -> f1, vs2
        | _ -> Binder (b1, [], f1, List.map (subst_annot sm) a), vs2)
    | Binder (b1, vs, f, a) when b1 <> b ->
        (match vs with
        | [] -> 
            let f1, vs1 = prop tvs f in
            Binder (b1, vs, f1, a), vs1
        | _ -> 
            let f1, vs1 = prop [] f in
            mk_binder ~ann:a b1 vs (mk_binder b vs1 f1), tvs)
    | f -> 
        let fv_f = fv f in
        f, List.filter (fun (x, _) -> IdSet.mem x fv_f) tvs
  in
  let f1, vs = prop [] f in 
  let res = mk_binder b vs f1 in
  res
 
(** Propagate existentially quantified variables upward in the formula [f].
 ** Assumes that [f] is in negation normal form. *)
let propagate_exists_up f = propagate_binder_up Exists f

(** Propagate universally quantified variables upward in the formula [f].
 ** Assumes that [f] is in negation normal form. *)
let propagate_forall_up f = propagate_binder_up Forall f

(** Propagate universally quantified variables downward in the formula [f].
 ** Assumes that [f] is in negation normal form. *)
let propagate_forall_down f =
  let rec prop bvs = function
    | BoolOp (And, fs) ->
        BoolOp (And, List.map (prop bvs) fs)
    | BoolOp (Or, fs) ->
        let fs1, fs2 =
          List.partition
            (fun f ->
              let fv_f = fv f in
              List.exists (fun (v, _) -> IdSet.mem v fv_f) bvs)
            fs
        in
        mk_or (mk_forall bvs (mk_or (List.map (prop []) fs1)) :: List.map (prop []) fs2)
    | Binder (b, [], f, ann) ->
        Binder (b, [], prop bvs f, ann)
    | Binder (Forall, bvs1, f, ann) ->
        let f1 = prop (bvs @ bvs1) f in
        annotate f1 ann
    | f -> mk_forall bvs f
  in prop [] f
    
(** Convert universal quantifiers in formula [f] into existentials where possible. *)
(** Assumes that [f] is in negation normal form. *)
let foralls_to_exists f =
  let rec find_defs bvs defs f =
    let rec disjoints_and_subsets dcs scs = function
      | BoolOp (Not, [Atom (App (SubsetEq, [t1; t2], _), _)]) :: fs ->
          let scs1 = orient_terms t1 t2 :: scs in
          disjoints_and_subsets dcs scs1 fs
      | BoolOp (Not, [Atom (App (Elem, [t1; t2], _), _)]) :: fs ->
          let scs1 = orient_terms (mk_setenum [t1]) t2 :: scs in
          disjoints_and_subsets dcs scs1 fs
      | BoolOp (Not, [Atom (App (Disjoint, [t1; t2], _), _)]) :: fs ->
          let dcs1 = orient_terms t1 t2 :: dcs in
          disjoints_and_subsets dcs1 scs fs
      | BoolOp (Or, gs) :: fs ->
          disjoints_and_subsets dcs scs (gs @ fs)
      | Binder (_, [], f, _) :: fs ->
          disjoints_and_subsets dcs scs (f :: fs)
      | _ :: fs ->
          disjoints_and_subsets dcs scs fs
      | [] -> dcs, scs
    in
    let dcs, scs = disjoints_and_subsets [] [] [f] in
    let rec find sm nodefs defs = function [@warning "-57"]
      | BoolOp (Not, [Atom (App (Eq, [Var (x, _) as xt; Var _ as yt], _), a)])
          when IdSet.mem x nodefs ->
            IdSet.remove x nodefs, mk_eq ~ann:a xt yt :: defs, mk_false, sm
      | BoolOp (Not, [Atom (App (Eq, [Var (x, _) as xt; t], _), a)])
        when IdSet.mem x nodefs && 
          IdSet.is_empty (IdSet.inter nodefs (fv_term t)) ->
            IdSet.remove x nodefs, mk_eq ~ann:a xt t :: defs, mk_false, sm
      | BoolOp (Not, [Atom (App (Eq, [t; Var (x, srt) as xt], _), a)])
        when IdSet.mem x nodefs && 
          IdSet.is_empty (IdSet.inter nodefs (fv_term t)) ->
            IdSet.remove x nodefs, mk_eq ~ann:a xt t :: defs, mk_false, sm
      | BoolOp (Not, [Atom (App (Eq, [t1; App (Union, [t2; (Var (x, _) as xt)], _)], _), _)])
      | BoolOp (Not, [Atom (App (Eq, [t1; App (Union, [(Var (x, _) as xt); t2], _)], _), _)])
        when IdSet.mem x nodefs &&
          List.mem (orient_terms xt t2) dcs &&
          IdSet.is_empty (IdSet.inter nodefs (fv_term_acc (fv_term t1) t2)) ->
            IdSet.remove x nodefs, mk_eq xt (mk_diff t1 t2) :: defs, mk_not (mk_subseteq t2 t1), sm
      | BoolOp (Not, [Atom (App (Eq, [(App (Diff, [xt; _], _) as t2); t1], _), _)])
      | BoolOp (Not, [Atom (App (Eq, [t1; (App (Diff, [xt; _], _) as t2)], _), _)])
        when not (IdSet.is_empty @@ IdSet.inter (fv_term xt) nodefs) &&
          IdSet.is_empty (IdSet.inter nodefs (fv_term t1)) ->
            let rec undiff ot t = match ot, t with
            | Some t, (Var (x, _) as xt) ->
                IdSet.remove x nodefs, mk_eq xt t :: defs, mk_false, sm
            | Some t, App (Diff, [t1; t2], _) when
                List.mem (orient_terms t1 t2) scs && IdSet.is_empty (IdSet.inter nodefs (fv_term t2)) ->
                  undiff (Some (mk_union [t; t2])) t1
            | _ -> nodefs, defs, f, sm
            in    
            undiff (Some t1) t2
      | BoolOp (Or, fs) ->
          let nodefs, defs, gs, sm =
            List.fold_right 
              (fun f (nodefs, defs, gs, sm) -> 
                let nodefs, defs, g, sm = find sm nodefs defs f in
                nodefs, defs, g :: gs, sm)
              fs (nodefs, defs, [], sm)
          in
          nodefs, defs, mk_or gs, sm
      | Binder (b, [], f, a) ->
          let nodefs, defs, g, sm = find sm nodefs defs f in
          let a = List.map (subst_annot sm) a in
          nodefs, defs, Binder (b, [], g, a), sm
      | f ->
          nodefs, defs, f, sm
    in
    let nodefs, defs, g, sm = find IdMap.empty bvs defs f in
    if IdSet.subset bvs nodefs 
    then begin
      let defs, sm, anns =
        List.fold_right (fun f (defs, sm, anns) ->
          match f with
          | Atom (App (Eq, [Var (v, _); t], _), a) ->
              let t1 = subst_term sm t in
              let smv = IdMap.singleton v t1 in
              let sm = IdMap.fold (fun w tw -> IdMap.add w (subst_term smv tw)) sm IdMap.empty in
              defs, IdMap.add v t1 sm, a @ anns
          | f -> f :: defs, sm, anns)
          defs ([], sm, [])
      in
      nodefs, List.map (subst sm) defs, annotate (subst sm g) (List.map (subst_annot sm) anns), sm
    end
    else find_defs nodefs defs g
  in
  let rec distribute_and gs = function
    | BoolOp (And, fs) :: gs1 ->
        let fs1 = List.map (fun f -> mk_or (List.rev_append gs (f :: gs1))) fs in
        let f1 = mk_and fs1 in
        (*print_endline "\nafter:";
        print_endline (string_of_form (mk_and fs));*)
        f1
    | BoolOp (Or, gs2) :: gs1 ->
        distribute_and gs (gs2 @ gs1)
    | [Binder (b, [], g, a)] ->
        let g1 = distribute_and gs [g] in
        Binder (b, [], g1, a)
    | Binder (_, [], g, a) :: gs1 ->
        (*assert (List.for_all (function TermGenerator _ -> false | _ -> true) a);*)
        distribute_and gs (g :: gs1)
    | g :: gs1 -> distribute_and (g :: gs) gs1
    | [] -> mk_or (List.rev gs)
  in
  let rec cf = function
    | Binder (b, [], f, a) ->
        Binder (b, [], cf f, a)
    | Binder (Forall, bvs, BoolOp (And, fs), a) ->
        let fs1 =
          List.rev
            (List.rev_map (fun f -> cf (Binder (Forall, bvs, f, a))) fs)
        in
        smk_and fs1
    | Binder (Forall, _, BoolOp (Or, _), _) as f ->
        (match propagate_forall_up f with
        | Binder (Forall, bvs, (BoolOp (Or, fs) as g0), a) ->
            let bvs_set = id_set_of_list (List.map fst bvs) in
            let nodefs, defs, g, sm = find_defs bvs_set [] g0 in
            let a = List.map (subst_annot sm) a in
            let ubvs, ebvs = List.partition (fun (x, _) -> IdSet.mem x nodefs) bvs in
            (match ebvs with
            | [] ->
                (*assert (List.for_all (function TermGenerator _ -> false | _ -> true) a);*)
                let f1 = mk_forall ~ann:a bvs (distribute_and [] [g]) in               
                if equal f f1 then f1 else cf f1
            | _ -> 
                let g1 = cf (mk_forall ubvs g) in
                smk_exists ~ann:a ebvs (mk_and (defs @ [g1])))
        | _ -> f)
    | Binder (Forall, bvs1, Binder (Forall, bvs2, f2, a2), a1) ->
        cf (Binder (Forall, bvs1 @ bvs2, f2, a1 @ a2))
    | Binder (Exists, bvs, f, a) ->
        smk_exists ~ann:a bvs (cf f)
    | BoolOp (And as op, fs)
    | BoolOp (Or as op, fs) ->
        let fs1 = List.map cf fs in
        BoolOp (op, fs1)
    | f -> f
  in
  cf f
    
    
(** Skolemize formula [f]. 
 ** Assumes that [f] is in negation normal form. *)
let skolemize f =
  let rec sk vs = function
    | BoolOp (op, fs) -> smk_op op (List.map (sk vs) fs)
    | Binder (Forall, bvs, f, a) ->
	let vs1 = 
	  List.fold_left 
	    (fun vs1 (id, srt) -> IdMap.add id srt vs1) vs bvs 
	in
	Binder (Forall, bvs, sk vs1 f, a)
    | Binder (Exists, bvs, f, a) ->
        let fv_f = fv f in
        let rel_vs = IdMap.filter (fun id _ -> IdSet.mem id fv_f) vs in
	let ts = IdMap.fold (fun id srt ts -> mk_var srt id :: ts) rel_vs [] in
	let sm = List.fold_left 
	    (fun sm (id, srt) -> 
	      let sk_fn = FreeSym (fresh_ident ("sk_" ^ (name id))) in
	      IdMap.add id (mk_app srt sk_fn ts) sm) 
	    IdMap.empty bvs
	in 
	annotate (subst sm (sk vs f)) (List.map (subst_annot sm) a)
    | f -> f
  in 
  let f1 = propagate_exists_up f in
  sk IdMap.empty f1

(** Make all names in formula [f] unique *)
let unique_names f =
  let mk_unique anns =
    List.map (function Name (n, _) -> Name (fresh_ident n) | a -> a) anns
  in
  let rec uc = function 
    | BoolOp (op, fs) -> BoolOp (op, List.map uc fs)
    | Binder (b, vs, f, anns) ->
        Binder (b, vs, uc f, mk_unique anns)
    | Atom (t, anns) -> Atom (t, mk_unique anns)
  in
  uc f

(** Give formula [f] a name if it does not already have one *)
let name_unnamed = 
  let unnamed = "unnamed" in
  fun f ->
    match f with
    | Binder (_, _, _, anns) 
    | Atom (_, anns) ->
        if List.exists (fun a -> match a with Name _ -> true | _ -> false) anns
        then f
        else mk_name unnamed f
    | f -> mk_name unnamed f
        
module Clauses = struct

  type clause = form list
  type clauses = clause list
       
  (** convert formula [f] into a set of clauses *)
  let from_form f : clauses = 
    let nf = cnf (nnf f) in
    let to_clause = function
      | BoolOp (Or, fs) -> fs
      | f -> [f]
    in
    match nf with
    | BoolOp (And, fs) -> List.map to_clause fs
    | f -> [to_clause f]
	  
  (** convert the set of clauses [cs] into a formula *)
  let to_form cs = smk_and (List.map smk_or cs)

end


(** Unit tests for GrassUtil.equal *)

(*let _ =
  let x = mk_ident "x" in
  let xvar = mk_var Int x in
  let y = mk_ident "y" in
  let yvar = mk_var Int y in
  let z = mk_ident "z" in
  let zvar = mk_var Int z in
  let p = mk_ident "p" in
  let f1 = mk_forall [x, Int] (mk_pred p [xvar]) in
  let f2 = mk_forall [y, Int] (mk_pred p [yvar]) in
  let f3 = mk_forall [y, Int] (mk_pred p [zvar]) in
  let h1 = mk_forall [(x, Int); (y, Int)] (mk_pred p [xvar; yvar]) in
  let h2 = mk_forall [(z, Int); (y, Int)] (mk_pred p [yvar; zvar]) in
  let h3 = mk_forall [(z, Int)] (mk_pred p [yvar; xvar]) in
  let h4 = mk_forall [(y, Int)] (mk_pred p [xvar; zvar]) in
  assert (equal f1 f1);
  assert (equal f1 f2);
  assert (equal f2 f1);
  assert (not @@ equal f1 f3);
  assert (equal h1 h2);
  assert (not @@ equal h3 h4)
*)

