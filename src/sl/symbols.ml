open Form
open Sl

type symbol = 
    { sym: string;
      arity: int;
      structure: Form.term (*domain*) -> Form.term list (*args*) -> Form.form;
      heap: Form.term (*domain*) -> Form.term list (*args*) -> Form.form;
    }

let symbols = Hashtbl.create 15

(* constructing the symbols from the input *)

let bound_id_to_var form =
  let rec process f = match f with
    | Form.Atom t -> Form.Atom t
    | BoolOp (b, lst) -> BoolOp(b, List.map process lst)
    | Binder (b, args, inner, annot) ->
      let inner = process inner in
      let args1 = List.map (fun ((name,version), srt) -> (("?"^name,version), srt) ) args in
      let map =
        List.fold_left2
          (fun acc (id, srt) (id2, _) -> IdMap.add id (FormUtil.mk_var id2 ~srt:srt) acc)
          IdMap.empty
          args
          args1
      in
      let inner = FormUtil.subst_consts map inner in
      let f2 = Binder(b, args1, inner, annot) in
        f2
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
      let f2 = FormUtil.subst_consts map f in
        f2
    )
  | _ -> failwith "expected first argument of type Set Loc (convention)."

let parsed_to_symbol (name, args, structure, heap) =
  let f1 = FormUtil.mk_comment ("structure of " ^ name) (FormTyping.typing (bound_id_to_var structure)) in
  let f2 = FormUtil.mk_comment ("domain of " ^ name) (FormTyping.typing (bound_id_to_var heap)) in
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

let pred_to_form p args domain =
  let pdef = get_symbol (str_of_ident p) in
  pdef.structure domain args, pdef.heap domain args

(* the predefined symbols *)

let predefined =
  [
    "emp(domain: set loc){" ^
        " true," ^
        "domain == {} }";
    "ptsTo(domain: set loc, ptr: fld loc, x: loc, y: loc){ " ^
        "ptr(x) == y, " ^
        "domain == {x} }";
    "lseg(domain: set loc, next: fld loc, x: loc, y: loc){ " ^
        "reach(next, x, y), " ^
        "forall l1: loc. l1 in domain <=> (btwn(next, x, l1, y) && l1 != y) }";
    "lseg_set(domain: set loc, next: fld loc, x: loc, y: loc, s: set loc){ " ^
        "reach(next, x, y), " ^
        "s == domain && (forall l1: loc. l1 in domain <=> (btwn(next, x, l1, y) && l1 != y)) }";
    "slseg(domain: set loc, data: fld int, next: fld loc, x: loc, y: loc){ " ^
        "reach(next, x, y) &&"^
        " forall l1: loc, l2: loc. (l1 in domain && l2 in domain && btwn(next, l1, l2, y)) ==> data(l1) <= data(l2), " ^
        "forall l1: loc. l1 in domain <=> (btwn(next, x, l1, y) && l1 != y) }";
    "rslseg(domain: set loc, data: fld int, next: fld loc, x: loc, y: loc){ " ^
        "reach(next, x, y) &&"^
        " forall l1: loc, l2: loc. (l1 in domain && l2 in domain && btwn(next, l1, l2, y)) ==> data(l1) >= data(l2), " ^
        "forall l1: loc.  l1 in domain <=> (btwn(next, x, l1, y) && l1 != y) }";
    "ulseg(domain: set loc, data: fld int, next: fld loc, x: loc, y: loc, v: int){ " ^
        "reach(next, x, y) && forall l1: loc. l1 in domain ==> data(l1) >= v, " ^
        " forall l1: loc. l1 in domain <=> (btwn(next, x, l1, y) && l1 != y) }";
    "llseg(domain: set loc, data: fld int, next: fld loc, x: loc, y: loc, v: int){ " ^
        "reach(next, x, y) && forall l1: loc. l1 in domain ==> data(l1) <= v, " ^
        "forall l1: loc. l1 in domain <=> (btwn(next, x, l1, y) && l1 != y) }";
    "uslseg(domain: set loc, data: fld int, next: fld loc, x: loc, y: loc, v: int){ " ^
        "reach(next, x, y) &&"^
        " (forall l1: loc. l1 in domain ==> data(l1) >= v) &&"^
        " forall l1: loc, l2: loc. (l1 in domain && l2 in domain && btwn(next, l1, l2, y)) ==> data(l1) <= data(l2),"^
        "forall l1: loc. l1 in domain <=> (btwn(next, x, l1, y) && l1 != y) }";
    "lslseg(domain: set loc, data: fld int, next: fld loc, x: loc, y: loc, v: int){" ^
        "reach(next, x, y) &&"^
        " (forall l1: loc. l1 in domain ==> data(l1) <= v) &&"^
        " forall l1: loc, l2: loc. (l1 in domain && l2 in domain && btwn(next, l1, l2, y)) ==> data(l1) <= data(l2),"^
        "forall l1: loc. l1 in domain <=> (btwn(next, x, l1, y) && l1 != y) }";
    "blseg(domain: set loc, data: fld int, next: fld loc, x: loc, y: loc, v: int, w: int){" ^
        "reach(next, x, y) && forall l1: loc. l1 in domain ==> (data(l1) >= v && data(l1) <= w)," ^
        "forall l1: loc. l1 in domain <=> (btwn(next, x, l1, y) && l1 != y) }";
    "bslseg(domain: set loc, data: fld int, next: fld loc, x: loc, y: loc, v: int, w: int){" ^
        "reach(next, x, y) &&"^
        " (forall l1: loc. l1 in domain ==> (data(l1) >= v && data(l1) <= w)) &&"^
        " forall l1: loc, l2: loc. (l1 in domain && l2 in domain && btwn(next, l1, l2, y)) ==> data(l1) <= data(l2)," ^
        "forall l1: loc. l1 in domain <=> (btwn(next, x, l1, y) && l1 != y) }";
    "dlseg(domain: set loc, next: fld loc, prev: fld loc, x1: loc, x2: loc, y1: loc, y2: loc){" ^
        "reach(next, x1, y1) &&" ^
        " ((x1 == y1 && x2 == y2) || (prev(x1) == x2 && next(y2) == y1 && y2 in domain)) &&" ^
        " forall l1: loc, l2: loc. (next(l1) == l2 && l1 in domain && l2 in domain) ==> prev(l2) == l1," ^
        "forall l1: loc. l1 in domain <=> (btwn(next, x1, l1, y1) && l1 != y1) }";
    "bdlseg(domain: set loc, data: fld int, next: fld loc, prev: fld loc, x1: loc, x2: loc, y1: loc, y2: loc, lb: int, ub:int){" ^
        "reach(next, x1, y1) &&" ^ 
        " ((x1 == y1 && x2 == y2) || (prev(x1) == x2 && next(y2) == y1 && y2 in domain)) &&"^
        (*" (forall l1: loc, l2: loc. (next(l1) == l2 && l1 in domain && l2 in domain) ==> prev(l2) == l1) &&"^*)
        " (forall l1: loc, l2: loc. (l1 in domain && l2 in domain) ==> (next(l1) == l2 <=> prev(l2) == l1)) &&"^
        " forall l1: loc. l1 in domain ==> (data(l1) >= lb && data(l1) <= ub)," ^
        "forall l1: loc. l1 in domain <=> (btwn(next, x1, l1, y1) && l1 != y1) }";
    "bsdlseg(domain: set loc, data: fld int, next: fld loc, prev: fld loc, x1: loc, x2: loc, y1: loc, y2: loc, lb: int, ub:int){" ^
        "reach(next, x1, y1) && ((x1 == y1 && x2 == y2) || (prev(x1) == x2 && next(y2) == y1 && y2 in domain)) && (forall l1: loc, l2: loc. (next(l1) == l2 && l1 in domain && l2 in domain) ==> prev(l2) == l1) && (forall l1: loc. l1 in domain ==> (data(l1) >= lb && data(l1) <= ub)) && forall l1: loc, l2: loc. (l1 in domain && l2 in domain && btwn(next, l1, l2, y)) ==> data(l1) <= data(l2)," ^
        "forall l1: loc. l1 in domain <=> (btwn(next, x1, l1, y1) && l1 != y1) }"
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
