open Form
open FormUtil

let di = mk_ident "domain"
let df = di, Set Loc
let d = mk_var ~srt:(snd df) (fst df)

let xf = mk_ident "x", Loc
let x = mk_var ~srt:(snd xf) (fst xf)

let yf = mk_ident "y", Loc
let y = mk_var ~srt:(snd yf) (fst yf)

let nextf = mk_ident "next", Fld Loc
let next = mk_var ~srt:(snd nextf) (fst nextf)

let l1f = mk_ident "l1", Loc
let l1 = mk_var ~srt:(snd l1f) (fst l1f)

let empty_loc = mk_empty (Some (Set Loc))

(* the predefined symbols *)
let without_fp = [
    ( mk_ident "emp",
      [df],
      mk_true,
      [di, mk_eq d empty_loc] );
    ( mk_ident "ptsTo",
      [df; nextf; xf; yf],
      mk_eq (mk_read next x) y,
      [di, mk_eq d (mk_setenum [x])]);
    ( mk_ident "lseg",
      [df; nextf; xf; yf],
      mk_reach next x y,
      [di, mk_forall [l1f] (mk_iff (mk_elem l1 d) (mk_and [(mk_btwn next x l1 y); (mk_neq l1 y)]))]);
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
