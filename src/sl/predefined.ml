open Form
open FormUtil

let di = mk_ident "domain"
let df = di, Set Loc
let d = mk_var ~srt:(snd df) (fst df)

let af = mk_ident "Alloc", Set Loc
let a = mk_var ~srt:(snd af) (fst af)

let xf = mk_ident "x", Loc
let x = mk_var ~srt:(snd xf) (fst xf)

let yf = mk_ident "y", Loc
let y = mk_var ~srt:(snd yf) (fst yf)

let mk_loc_field name = 
  let fieldf = mk_ident name, Fld Loc in
  let field = mk_var ~srt:(snd fieldf) (fst fieldf) in
  fieldf, field

let nextf, next = mk_loc_field "next"

let leftf, left = mk_loc_field "left"

let rightf, right = mk_loc_field "right"

let parentf, parent = mk_loc_field "parent"

let l1f = mk_ident "l1", Loc
let l1 = mk_var ~srt:(snd l1f) (fst l1f)

let l2f = mk_ident "l2", Loc
let l2 = mk_var ~srt:(snd l2f) (fst l2f)

let l3f = mk_ident "l3", Loc
let l3 = mk_var ~srt:(snd l3f) (fst l3f)

let empty_loc = mk_empty (Some (Set Loc))

(* the predefined symbols *)
let without_fp = [
    ( mk_ident "emp",
      [df],
      mk_true,
      [di, mk_eq d empty_loc] );
    ( mk_ident "lseg",
      [df; af; nextf; xf; yf],
      mk_reach next x y,
      [di, mk_forall [l1f] (mk_iff (mk_elem l1 d) (mk_and [(mk_btwn next x l1 y); (mk_neq l1 y)]))]);
    ( mk_ident "tree",
      [df; af; leftf; parentf; rightf; xf; yf],
      mk_or [mk_eq x mk_null;
             mk_and [mk_neq x mk_null; 
                     mk_eq (mk_read parent x) y;
                     mk_forall ~ann:([Comment "parent_left_or_right_equal"]) [l1f; l2f; l3f] 
                       (mk_sequent 
                          [mk_eq l2 l3; mk_elem l1 d; mk_elem l2 d; mk_eq (mk_read parent l1) l2] 
                          [mk_eq l1 x; mk_eq (mk_read left l2) l1; mk_eq (mk_read right l3) l1]);
                     mk_forall ~ann:([Comment "left_parent_equal"]) [l1f; l2f] 
                       (mk_sequent 
                          [mk_elem l1 d; mk_elem l2 d; mk_eq (mk_read left l1) l2]
                          [mk_eq l2 mk_null; mk_eq (mk_read parent l2) l1]);
                     mk_forall ~ann:([Comment "right_parent_equal"]) [l1f; l2f] 
                       (mk_sequent
                          [mk_elem l1 d; mk_elem l2 d; mk_eq (mk_read right l1) l2]
                          [mk_eq l2 mk_null; mk_eq (mk_read parent l2) l1]);
                     mk_forall ~ann:([Comment "left_right_distinct"]) [l1f; l2f]
                       (mk_sequent
                          [mk_elem l1 d; mk_eq l1 l2; mk_eq (mk_read left l1) (mk_read right l2)]
                          [mk_eq mk_null (mk_read left l1)]);
                     mk_forall ~ann:([Comment "left_leaf"]) [l1f]
                       (mk_sequent
                          [mk_elem l1 d] 
                          [mk_elem (mk_read left l1) a; mk_eq (mk_read left l1) mk_null]);
                     mk_forall ~ann:([Comment "right_leaf"]) [l1f]
                       (mk_sequent
                          [mk_elem l1 d] 
                          [mk_elem (mk_read right l1) a; mk_eq (mk_read right l1) mk_null]);                   ] 
           ],
      [di, mk_or [mk_and [mk_eq x mk_null; mk_eq d empty_loc]; 
                  mk_and [mk_neq x mk_null; mk_forall [l1f] 
                            (mk_iff (mk_elem l1 d) (mk_and [mk_elem l1 a; mk_reach parent l1 x]))]]]
     ) (* end of "tree" *)
  ]

let with_fp = []
let with_content = []
let misc = []

(*
let without_fp =
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

let with_fp =
  [
    "lseg_set(domain: set loc, next: fld loc, x: loc, y: loc, s: set loc){ " ^
        "reach(next, x, y), " ^
        "s == domain && (forall l1: loc. l1 in domain <=> (btwn(next, x, l1, y) && l1 != y)) }";
    "slseg_set(domain: set loc, data: fld int, next: fld loc, x: loc, y: loc, s: set loc){ " ^
        "reach(next, x, y) &&"^
        " forall l1: loc, l2: loc. (l1 in domain && l2 in domain && btwn(next, l1, l2, y)) ==> data(l1) <= data(l2), " ^
        "s == domain && (forall l1: loc. l1 in domain <=> (btwn(next, x, l1, y) && l1 != y)) }";
    "rslseg_set(domain: set loc, data: fld int, next: fld loc, x: loc, y: loc, s: set loc){ " ^
        "reach(next, x, y) &&"^
        " forall l1: loc, l2: loc. (l1 in domain && l2 in domain && btwn(next, l1, l2, y)) ==> data(l1) >= data(l2), " ^
        "s == domain && (forall l1: loc.  l1 in domain <=> (btwn(next, x, l1, y) && l1 != y)) }";
    "uslseg_set(domain: set loc, data: fld int, next: fld loc, x: loc, y: loc, v: int, s: set loc){ " ^
        "reach(next, x, y) &&"^
        " (forall l1: loc. l1 in domain ==> data(l1) >= v) &&"^
        " forall l1: loc, l2: loc. (l1 in domain && l2 in domain && btwn(next, l1, l2, y)) ==> data(l1) <= data(l2),"^
        "s == domain && (forall l1: loc. l1 in domain <=> (btwn(next, x, l1, y) && l1 != y)) }";
    "lslseg_set(domain: set loc, data: fld int, next: fld loc, x: loc, y: loc, v: int, s: set loc){" ^
        "reach(next, x, y) &&"^
        " (forall l1: loc. l1 in domain ==> data(l1) <= v) &&"^
        " forall l1: loc, l2: loc. (l1 in domain && l2 in domain && btwn(next, l1, l2, y)) ==> data(l1) <= data(l2),"^
        "s == domain && (forall l1: loc. l1 in domain <=> (btwn(next, x, l1, y) && l1 != y)) }";
    "bslseg_set(domain: set loc, data: fld int, next: fld loc, x: loc, y: loc, v: int, w: int, s: set loc){" ^
        "reach(next, x, y) &&"^
        " (forall l1: loc. l1 in domain ==> (data(l1) >= v && data(l1) <= w)) &&"^
        " forall l1: loc, l2: loc. (l1 in domain && l2 in domain && btwn(next, l1, l2, y)) ==> data(l1) <= data(l2)," ^
        "s == domain && (forall l1: loc. l1 in domain <=> (btwn(next, x, l1, y) && l1 != y)) }"
  ]

let with_content =
  [
    "slseg_content(domain: set loc, data: fld int, next: fld loc, x: loc, y: loc, s: set int){ " ^
        "reach(next, x, y) &&"^
        " (forall l1: loc. l1 in domain <=> data(l1) in s) &&"^
        " forall l1: loc, l2: loc. (l1 in domain && l2 in domain && btwn(next, l1, l2, y)) ==> data(l1) <= data(l2), " ^
        " (forall l1: loc. data(l1) in s <=> (btwn(next, x, l1, y) && l1 != y)) &&"^
        " (forall l1: loc. l1 in domain <=> (btwn(next, x, l1, y) && l1 != y)) }";
    "rslseg_content(domain: set loc, data: fld int, next: fld loc, x: loc, y: loc, s: set int){ " ^
        "reach(next, x, y) &&"^
        " (forall l1: loc. l1 in domain <=> data(l1) in s) &&"^
        " forall l1: loc, l2: loc. (l1 in domain && l2 in domain && btwn(next, l1, l2, y)) ==> data(l1) >= data(l2), " ^
        " (forall l1: loc.  l1 in domain <=> (btwn(next, x, l1, y) && l1 != y)) }";
    "uslseg_content(domain: set loc, data: fld int, next: fld loc, x: loc, y: loc, v: int, s: set int){ " ^
        "reach(next, x, y) &&"^
        " (forall l1: loc. l1 in domain ==> data(l1) >= v) &&"^
        " (forall l1: loc. l1 in domain <=> data(l1) in s) &&"^
        " forall l1: loc, l2: loc. (l1 in domain && l2 in domain && btwn(next, l1, l2, y)) ==> data(l1) <= data(l2),"^
        " (forall l1: loc. l1 in domain <=> (btwn(next, x, l1, y) && l1 != y)) }";
    "lslseg_content(domain: set loc, data: fld int, next: fld loc, x: loc, y: loc, v: int, s: set int){" ^
        "reach(next, x, y) &&"^
        " (forall l1: loc. l1 in domain ==> data(l1) <= v) &&"^
        " (forall l1: loc. l1 in domain <=> data(l1) in s) &&"^
        " forall l1: loc, l2: loc. (l1 in domain && l2 in domain && btwn(next, l1, l2, y)) ==> data(l1) <= data(l2),"^
        " (forall l1: loc. l1 in domain <=> (btwn(next, x, l1, y) && l1 != y)) }";
    "bslseg_content(domain: set loc, data: fld int, next: fld loc, x: loc, y: loc, v: int, w: int, s: set int){" ^
        "reach(next, x, y) &&"^
        " (forall l1: loc. l1 in domain ==> (data(l1) >= v && data(l1) <= w)) &&"^
        " (forall l1: loc. l1 in domain <=> data(l1) in s) &&"^
        " forall l1: loc, l2: loc. (l1 in domain && l2 in domain && btwn(next, l1, l2, y)) ==> data(l1) <= data(l2)," ^
        " (forall l1: loc. l1 in domain <=> (btwn(next, x, l1, y) && l1 != y)) }"
  ]

let misc = [
    "sorted_set(domain: set loc, data: fld int, next: fld loc, x: loc, y: loc, v: int, w: int, s: set loc){" ^
        "reach(next, x, y) &&"^
        " (forall l1: loc. l1 in domain ==> (data(l1) >= v && data(l1) <= w)) &&"^
        " forall l1: loc, l2: loc. (l1 in domain && l2 in domain && btwn(next, l1, l2, y)) ==> data(l1) <= data(l2)," ^
        "s == domain && (forall l1: loc. l1 in domain <=> (btwn(next, x, l1, y) && l1 != y)) }"
  ]
*)

let symbols = without_fp @ with_fp @ with_content @ misc
