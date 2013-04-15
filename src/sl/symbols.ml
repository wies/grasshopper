open Form
open Sl

let symbols = Hashtbl.create 15

(* part to know what symbol has what field *)

let fields = Hashtbl.create 15

let rec get_field f = match f with
  | Not t -> get_field t
  | Spatial (d, _) ->
    begin
      try Hashtbl.find fields d.sym
      with Not_found -> IdSrtSet.empty
    end
  | Pure _ -> IdSrtSet.empty
  | SepConj lst | And lst | Or lst -> 
    List.fold_left (fun acc f -> IdSrtSet.union acc (get_field f)) IdSrtSet.empty lst

let rec get_fields f = 
  let flds = get_field f in
    IdSrtSet.fold
      (fun (f, t) acc -> (FormUtil.mk_free_const f ~srt:t) :: acc)
      flds
      []

let get_fields_loc f =
  let flds = get_field f in
    IdSrtSet.fold
      (fun (f, t) acc -> if t = Form.Fld Form.Loc then f::acc else acc)
      flds
      []

let get_fields_data f =
  let flds = get_field f in
    IdSrtSet.fold
      (fun (f, t) acc -> if t = Form.Fld Form.Int then f::acc else acc)
      flds
      []

(* constructing the symbols from the input *)

let bound_id_to_var form =
  let rec process f = match f with
    | Atom t -> Atom t
    | BoolOp (b, lst) -> BoolOp(b, List.map process lst)
    | Binder (b, args, f, annot) ->
      let f2 = process f in
      let map =
        List.fold_left
          (fun acc (id, srt) -> IdMap.add id (FormUtil.mk_var id ~srt:srt) acc)
          IdMap.empty
          args
      in
      let f3 = FormUtil.subst_consts map f2 in
        Binder(b, args, f3, annot)
  in
    process form

let apply args f = match args with
  | (id, Set Loc) :: args ->
    (fun domain terms ->
      assert(List.length args = List.length terms);
      let map =
        List.fold_left2
          (fun acc (id, _) term -> IdMap.add id term acc)
          (IdMap.add id domain IdMap.empty)
          args
          terms
      in
        FormUtil.subst_consts map f
    )
  | _ -> failwith "expected first argument of type Set Loc (convention)."

let get_flds name args f =
  let csts = List.map (fun (id, srt) -> FormUtil.mk_free_const id ~srt:srt) args in
  let arg_cstr = List.map (fun c -> FormUtil.mk_eq c c) csts in
  let f2 = FormUtil.mk_and (f :: arg_cstr) in
  let typed = FormTyping.typing f2 in (* this last catches the typing errors *)
  let sign = FormUtil.overloaded_sign typed in
  let flds =
    SymbolMap.fold
      (fun k v acc ->
        List.fold_left
          (fun acc t -> match (k, t) with
            | (FreeSym id, ([], (Fld _ as t))) -> IdSrtSet.add (id, t) acc
            | _ -> acc
          )
          acc
          v
      )
      sign
      IdSrtSet.empty
  in
  let old = try Hashtbl.find fields name with Not_found -> IdSrtSet.empty in
    Hashtbl.add fields name (IdSrtSet.union flds old)

let parsed_to_symbol (name, args, structure, heap) =
  get_flds name args structure;
  get_flds name args heap;
  let f1 = FormUtil.mk_comment ("strucure_of_"^name) (bound_id_to_var structure) in
  let f2 = FormUtil.mk_comment ("heap_of_"^name) (bound_id_to_var heap) in
  let a = (List.length args) - 1 in
    assert(a >= 0);
    { sym = name;
      arity = a;
      structure = apply args f1;
      heap = apply args f2
    }

let get_symbol s = Hashtbl.find symbols s

let find_symbol s =
  try Some (Hashtbl.find symbols s)
  with Not_found -> None

let arity s = match find_symbol s with
  | Some s -> Some s.arity
  | None -> None

let symbol_to_string s = match find_symbol s with
  | Some s -> Some s.sym
  | None -> None

(* the predefined symbols *)

let predefined =
  [
    "emp(domain: set loc){ true, domain == {} }";
    "ptsTo(domain: set loc, f: fld loc, x: loc, y: loc){ next(x) == y, domain == {x} }";
    "lseg(domain: set loc, x: loc, y: loc){ reach(x, y), forall l1: loc. l1 in domain <=> (btwn(x, l1, y) && l1 != y) }";
    "slseg(domain: set loc, x: loc, y: loc){ reach(x, y) && forall l1: loc, l2: loc. (l1 in domain && l2 in domain && reach( l1, l2)) ==> data(l1) <= data(l2), forall l1: loc. l1 in domain <=> (btwn(x, l1, y) && l1 != y) }";
    "rslseg(domain: set loc, x: loc, y: loc){ reach(x, y) && forall l1: loc, l2: loc. (l1 in domain && l2 in domain && reach( l1, l2)) ==> data(l1) >= data(l2), forall l1: loc.  l1 in domain <=> (btwn(x, l1, y) && l1 != y) }";
    "ulseg(domain: set loc, x: loc, y: loc, v: int){ reach(x, y) && forall l1: loc. l1 in domain ==> data(l1) >= v, forall l1: loc. l1 in domain <=> (btwn(x, l1, y) && l1 != y) }";
    "llseg(domain: set loc, x: loc, y: loc, v: int){ reach(x, y) && forall l1: loc. l1 in domain ==> data(l1) <= v, forall l1: loc. l1 in domain <=> (btwn(x, l1, y) && l1 != y) }";
    "uslseg(domain: set loc, x: loc, y: loc, v: int){ reach(x, y) && (forall l1: loc. l1 in domain ==> data(l1) >= v) && forall l1: loc, l2: loc. (l1 in domain && l2 in domain && reach( l1, l2)) ==> data(l1) <= data(l2), forall l1: loc. l1 in domain <=> (btwn(x, l1, y) && l1 != y) }";
    "lslseg(domain: set loc, x: loc, y: loc, v: int){ reach(x, y) && (forall l1: loc. l1 in domain ==> data(l1) <= v) && forall l1: loc, l2: loc. (l1 in domain && l2 in domain && reach( l1, l2)) ==> data(l1) <= data(l2), forall l1: loc. (btwn(x, l1, y) && l1 != y) }";
    "blseg(domain: set loc, x: loc, y: loc, v: int, w: int){ reach(x, y) && forall l1: loc. l1 in domain ==> (data(l1) >= v && data(l1) <= w), forall l1: loc. l1 in domain <=> (btwn(x, l1, y) && l1 != y) }";
    "bslseg(domain: set loc, x: loc, y: loc, v: int, w: int){ reach(x, y) && (forall l1: loc. l1 in domain ==> (data(l1) >= v && data(l1) <= w)) && forall l1: loc, l2: loc. (l1 in domain && l2 in domain && reach( l1, l2)) ==> data(l1) <= data(l2), forall l1: loc. l1 in domain <=> (btwn(x, l1, y) && l1 != y) }";
    "dlseg(domain: set loc, x1: loc, x2: loc, y1: loc, y2: loc){ reach(x1, y1) && ((x1 == y1 && x2 == y2) || (prev(x1) == x2 && next(y2) == y1 && y1 in domain)) && forall l1: loc. next(l1) in domain ==> prev(next(l1)) == l1,  forall l1: loc. l1 in domain <=> (btwn(x1, l1, y1) && l1 != y1) }"
  ]

(* add the predefined symbols *)
let _ =
  List.iter
    (fun str ->
      ParseError.input := Some str;
      let lexbuf = Lexing.from_string str in
      ParseError.buffer := Some lexbuf;
      let parsed = ParseDef.main LexDef.token lexbuf in
      let syms = List.map parsed_to_symbol parsed in
        List.iter (fun s -> Hashtbl.add symbols s.sym s) syms
    )
    predefined

(*
let emp   =
  { sym = "emp";
    arity = 0;
    structure = (fun _ _ -> FormUtil.mk_true);
    heap = (fun domain _ -> empty domain)
  }

let ptsTo =
  { sym = "ptsTo";
    arity = 3;
    structure = (fun _ args -> match args with
        | [h; id1; id2] -> FormUtil.mk_eq (FormUtil.mk_read h id1) id2
        | _ -> failwith "wrong number of arguments");
    heap = (fun domain args ->  match args with
        | [_; id1; _] -> FormUtil.mk_eq (mk_loc_set domain) (FormUtil.mk_setenum [id1])
        | _ -> failwith "wrong number of arguments");
  }

let lseg  =
  { sym = "lseg";
    arity = 2;
    structure = (fun _ args -> match args with
        | [id1; id2] ->  reach id1 id2
        | _ -> failwith "wrong number of arguments");
    heap = (fun domain args ->  match args with
        | [id1; id2] ->
            Axioms.mk_axiom 
              ("def_of_" ^ Form.str_of_ident domain) 
              (list_set_def id1 id2 domain)    
        | _ -> failwith "wrong number of arguments");
  }

let slseg =
  { sym = "slseg";
    arity = 2;
    structure = (fun domain args -> match args with
        | [id1; id2] -> 
            let part1 = reach id1 id2 in
            let part2 = 
              Axioms.mk_axiom
                ("sls_" ^ Form.str_of_ident domain)
                (sorted domain)
            in
              FormUtil.mk_and [part1; part2]
        | _ -> failwith "wrong number of arguments");
    heap = (fun domain args ->  match args with
        | [id1; id2] ->
            Axioms.mk_axiom 
              ("def_of_" ^ Form.str_of_ident domain) 
              (list_set_def id1 id2 domain)    
        | _ -> failwith "wrong number of arguments");
  }

let rslseg =
  { sym = "rslseg";
    arity = 2;
    structure = (fun domain args -> match args with
        | [id1; id2] -> 
            let part1 = reach id1 id2 in
            let part2 = 
              Axioms.mk_axiom ("rsls_" ^ Form.str_of_ident domain)
                (FormUtil.mk_implies
                  (FormUtil.mk_and [mk_domain domain Axioms.loc1;
                                    mk_domain domain Axioms.loc2;
                                    reach Axioms.loc1 Axioms.loc2])
                  (FormUtil.mk_geq (get_data Axioms.loc1) (get_data Axioms.loc2)))
            in
              FormUtil.mk_and [part1; part2]
        | _ -> failwith "wrong number of arguments");
    heap = (fun domain args ->  match args with
        | [id1; id2] ->
            Axioms.mk_axiom 
              ("def_of_" ^ Form.str_of_ident domain) 
              (list_set_def id1 id2 domain)    
        | _ -> failwith "wrong number of arguments");
  }

let ulseg =
  { sym = "ulseg";
    arity = 3;
    structure = (fun domain args -> match args with
        | [id1; id2; id3] -> 
            let part1 = reach id1 id2 in
            let part2 = 
              Axioms.mk_axiom
                ("uls_" ^ Form.str_of_ident domain)
                (lower_bound domain id3)
            in
              FormUtil.mk_and [part1; part2]
        | _ -> failwith "wrong number of arguments");
    heap = (fun domain args ->  match args with
        | [id1; id2; _] ->
            Axioms.mk_axiom 
              ("def_of_" ^ Form.str_of_ident domain) 
              (list_set_def id1 id2 domain)    
        | _ -> failwith "wrong number of arguments");
  }

let llseg =
  { sym = "llseg";
    arity = 3;
    structure = (fun domain args -> match args with
        | [id1; id2; id3] -> 
            let part1 = reach id1 id2 in
            let part2 = 
              Axioms.mk_axiom
                ("lls_" ^ Form.str_of_ident domain)
                (upper_bound domain id3)
            in
              FormUtil.mk_and [part1; part2]
        | _ -> failwith "wrong number of arguments");
    heap = (fun domain args ->  match args with
        | [id1; id2; _] ->
            Axioms.mk_axiom 
              ("def_of_" ^ Form.str_of_ident domain) 
              (list_set_def id1 id2 domain)    
        | _ -> failwith "wrong number of arguments");
  }

let uslseg =
  { sym = "uslseg";
    arity = 3;
    structure = (fun domain args -> match args with
        | [id1; id2; id3] -> 
            let part1 = reach id1 id2 in
            let part2 = 
              Axioms.mk_axiom
                ("usls_bound_" ^ Form.str_of_ident domain)
                (lower_bound domain id3)
            in
            let part3 =
              Axioms.mk_axiom
                ("usls_sort_" ^ Form.str_of_ident domain)
                (sorted domain)
            in
              FormUtil.mk_and [part1; part2; part3]
        | _ -> failwith "wrong number of arguments");
    heap = (fun domain args ->  match args with
        | [id1; id2; _] ->
            Axioms.mk_axiom 
              ("def_of_" ^ Form.str_of_ident domain) 
              (list_set_def id1 id2 domain)    
        | _ -> failwith "wrong number of arguments");
  }

let lslseg =
  { sym = "lslseg";
    arity = 3;
    structure = (fun domain args -> match args with
        | [id1; id2; id3] -> 
            let part1 = reach id1 id2 in
            let part2 = 
              Axioms.mk_axiom ("lsls_bound_" ^ Form.str_of_ident domain)
                (upper_bound domain id3)
            in
            let part3 =
              Axioms.mk_axiom ("lsls_sort_" ^ Form.str_of_ident domain)
                (sorted domain)
            in
              FormUtil.mk_and [part1; part2; part3]
        | _ -> failwith "wrong number of arguments");
    heap = (fun domain args ->  match args with
        | [id1; id2; _] ->
            Axioms.mk_axiom 
              ("def_of_" ^ Form.str_of_ident domain) 
              (list_set_def id1 id2 domain)    
        | _ -> failwith "wrong number of arguments");
  }

let dlseg =
  { sym = "dlseg";
    arity = 4;
    structure = (fun domain args -> match args with
        | [x1; x2; y1; y2] -> 
            let part1 = reach x1 y1 in
            let part2 =
              Axioms.mk_axiom ("dll_" ^ Form.str_of_ident domain)
                (FormUtil.mk_implies (FormUtil.mk_and [ mk_domain domain Axioms.loc1;
                                                        mk_domain domain Axioms.loc2;
                                                        FormUtil.mk_eq (FormUtil.mk_read fpts Axioms.loc1) Axioms.loc2])
                   (FormUtil.mk_eq (FormUtil.mk_read fprev_pts Axioms.loc2) Axioms.loc1)) in
            let part3 =
              FormUtil.mk_or [
              FormUtil.mk_and [ FormUtil.mk_eq x1 y1; FormUtil.mk_eq x2 y2];
              FormUtil.mk_and [ FormUtil.mk_eq (FormUtil.mk_read fprev_pts x1) x2;
                                FormUtil.mk_eq (FormUtil.mk_read fpts y2) y1;
                                mk_domain domain y2] ]
            in
              FormUtil.mk_and [part1; part2; part3]
        | _ -> failwith "wrong number of arguments");
    heap = (fun domain args ->  match args with
        | [id1; _; id2; _] ->
            Axioms.mk_axiom 
              ("def_of_" ^ Form.str_of_ident domain) 
              (list_set_def id1 id2 domain)    
        | _ -> failwith "wrong number of arguments");
  }

let blseg =
  { sym = "blseg";
    arity = 4;
    structure = (fun domain args -> match args with
        | [id1; id2; id3; id4] -> 
            let part1 = reach id1 id2 in
            let part2 = 
              Axioms.mk_axiom ("bsls_upper_bound_" ^ Form.str_of_ident domain)
                (upper_bound domain id4)
            in
            let part4 = 
              Axioms.mk_axiom ("bsls_lower_bound_" ^ Form.str_of_ident domain)
                (lower_bound domain id3)
            in
              FormUtil.mk_and [part1; part2; part4]
        | _ -> failwith "wrong number of arguments");
    heap = (fun domain args ->  match args with
        | [id1; id2; _; _] ->
            Axioms.mk_axiom 
              ("def_of_" ^ Form.str_of_ident domain) 
              (list_set_def id1 id2 domain)    
        | _ -> failwith "wrong number of arguments");
  }

let bslseg =
  { sym = "bslseg";
    arity = 4;
    structure = (fun domain args -> match args with
        | [id1; id2; id3; id4] -> 
            let part1 = reach id1 id2 in
            let part2 = 
              Axioms.mk_axiom ("bsls_upper_bound_" ^ Form.str_of_ident domain)
                (upper_bound domain id4)
            in
            let part3 =
              Axioms.mk_axiom ("lsls_sort_" ^ Form.str_of_ident domain)
                (sorted domain)
            in
            let part4 = 
              Axioms.mk_axiom ("bsls_lower_bound_" ^ Form.str_of_ident domain)
                (lower_bound domain id3)
            in
              FormUtil.mk_and [part1; part2; part3; part4]
        | _ -> failwith "wrong number of arguments");
    heap = (fun domain args ->  match args with
        | [id1; id2; _; _] ->
            Axioms.mk_axiom 
              ("def_of_" ^ Form.str_of_ident domain) 
              (list_set_def id1 id2 domain)    
        | _ -> failwith "wrong number of arguments");
  }

let symbols =
  [ emp;
    ptsTo;
    lseg;
    slseg;
    rslseg;
    ulseg;
    llseg;
    uslseg;
    lslseg;
    dlseg;
    blseg;
    bslseg
  ]
*)
