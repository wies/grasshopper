open Form
open FormUtil

let mk_formal_and_var name tpe =
  let i = mk_ident name in
  let f = i, tpe in
  let v = mk_var ~srt:tpe i in
    i, f, v

let mk_loc name = mk_formal_and_var name Loc
let mk_int name = mk_formal_and_var name Int
let mk_loc_field name = mk_formal_and_var name (Fld Loc)
let mk_int_field name = mk_formal_and_var name (Fld Int)

let di, df, d = mk_formal_and_var "domain" (Set Loc)

let si, sf, s = mk_formal_and_var "S" (Set Loc)

let _, xf, x = mk_loc "x"
let _, yf, y = mk_loc "y"
let _, x1f, x1 = mk_loc "x1"
let _, y1f, y1 = mk_loc "y1"
let _, x2f, x2 = mk_loc "x2"
let _, y2f, y2 = mk_loc "y2"

let _, lbf, lb = mk_int "lb"
let _, ubf, ub = mk_int "ub"

let _, nextf, next = mk_loc_field "next"
let _, prevf, prev = mk_loc_field "prev"
let _, leftf, left = mk_loc_field "left"
let _, rightf, right = mk_loc_field "right"
let _, parentf, parent = mk_loc_field "parent"

let _, dataf, data = mk_int_field "data"

let _, l1f, l1 = mk_loc "l1"
let _, l2f, l2 = mk_loc "l2"
let _, l3f, l3 = mk_loc "l3"

let empty_loc = mk_empty (Some (Set Loc))

(* short hand*)
let l1_in_domain = mk_elem l1 d
let l2_in_domain = mk_elem l2 d
let l1_in_lst_fp = mk_and [mk_btwn next x l1 y; mk_neq l1 y]

(* the predefined symbols *)
let without_fp = [
    ( mk_ident "emp",
      [df],
      mk_true,
      [di, mk_eq d empty_loc] );
    ( mk_ident "treeNodes",
      [df; leftf; parentf; rightf; sf],
      mk_and [(*mk_forall [l1f] (mk_reach parent l1 mk_null);*)
              (*mk_or [mk_eq x mk_null; mk_eq (mk_read parent x) y];*)
              mk_forall ~ann:([Comment "parent_left_or_right_equal"]) [l1f; l2f; l3f] 
                (mk_sequent 
                   [mk_eq l2 l3; mk_elem l1 s; mk_eq (mk_read parent l1) l2] 
                   [mk_eq l2 mk_null; mk_eq (mk_read left l2) l1; mk_eq (mk_read right l3) l1]);
              (let left_parent_generator =
                [TermGenerator 
                   ([l1f],
                    [],
                    [Match (mk_read left l1, FilterTrue)],
                    mk_read parent (mk_read left l1));
               ]
              in
              mk_forall ~ann:(Comment "left_parent_equal" :: left_parent_generator) [l1f; l2f] 
                (mk_sequent 
                   [mk_elem l1 s; mk_eq (mk_read left l1) l2]
                   [mk_eq l2 mk_null; mk_eq (mk_read parent l2) l1]));
              (let right_parent_generator =
                [TermGenerator 
                   ([l1f],
                    [],
                    [Match (mk_read right l1, FilterTrue)],
                    mk_read parent (mk_read right l1));
               ]
              in
              mk_forall ~ann:(Comment "right_parent_equal" :: right_parent_generator) [l1f; l2f] 
                (mk_sequent
                   [mk_elem l1 s; mk_eq (mk_read right l1) l2]
                   [mk_eq l2 mk_null; mk_eq (mk_read parent l2) l1]));
              mk_forall ~ann:([Comment "left_right_distinct"]) [l1f; l2f]
                (mk_sequent
                   [mk_elem l1 s; mk_eq l1 l2; mk_eq (mk_read left l1) (mk_read right l2)]
                   [mk_eq mk_null (mk_read left l1)]);
              mk_forall ~ann:([Comment "parent_outside_null"]) [l1f; l2f]
                (mk_sequent
                   [mk_reach parent l1 l2]
                   [mk_eq l1 l2; mk_elem l1 s; mk_eq l2 mk_null]);
              mk_forall ~ann:[Comment "reach_via_left_right"] [l1f; l2f]
                (mk_sequent 
                   [mk_reach parent l1 l2; mk_elem l1 d; mk_elem l2 d]
                   [mk_eq l1 l2;
                    mk_btwn parent l1 (mk_read left l2) l2;
                    mk_btwn parent l1 (mk_read right l2) l2])
            ],
      [di, mk_eq d empty_loc]);
    ( mk_ident "tree",
      [df; leftf; parentf; rightf; xf],
      mk_true,
      [di, mk_forall ~ann:([Comment "tree_footprint"]) [l1f] (mk_iff l1_in_domain (mk_and [mk_btwn parent l1 x x; mk_neq l1 mk_null]))]);
    ( mk_ident "treeFP",
      [df; leftf; parentf; rightf; xf; sf],
      mk_true,
      [di, mk_forall ~ann:([Comment "tree_footprint"]) [l1f] (mk_iff l1_in_domain (mk_and [mk_btwn parent l1 x x; mk_neq x mk_null]));
       si, mk_forall [l1f] (mk_iff (mk_elem l1 s) (mk_and [mk_btwn parent l1 x x; mk_neq x mk_null]))]);
    (*
    ( mk_ident "tree",
      [df; leftf; parentf; rightf; xf; yf],
      mk_and [(*mk_forall [l1f] (mk_reach parent l1 mk_null);*)
              mk_or [mk_eq x mk_null; mk_eq (mk_read parent x) y];
              mk_forall ~ann:([Comment "parent_left_or_right_equal"]) [l1f; l2f; l3f] 
                (mk_sequent 
                   [mk_eq l2 l3; mk_elem l1 d; mk_eq (mk_read parent l1) l2] 
                   [mk_eq l1 x; mk_eq (mk_read left l2) l1; mk_eq (mk_read right l3) l1]);
              (let left_parent_generator =
                [TermGenerator 
                   ([l1f],
                    [],
                    [Match (mk_read left l1, FilterTrue)],
                    mk_read parent (mk_read left l1));
               ]
              in
              mk_forall ~ann:(Comment "left_parent_equal" :: left_parent_generator) [l1f; l2f] 
                (mk_sequent 
                   [mk_elem l1 d; mk_eq (mk_read left l1) l2]
                   [mk_eq l2 mk_null; mk_eq (mk_read parent l2) l1]));
              (let right_parent_generator =
                [TermGenerator 
                   ([l1f],
                    [],
                    [Match (mk_read right l1, FilterTrue)],
                    mk_read parent (mk_read right l1));
               ]
              in
              mk_forall ~ann:(Comment "right_parent_equal" :: right_parent_generator) [l1f; l2f] 
                (mk_sequent
                   [mk_elem l1 d; mk_eq (mk_read right l1) l2]
                   [mk_eq l2 mk_null; mk_eq (mk_read parent l2) l1]));
              mk_forall ~ann:([Comment "left_right_distinct"]) [l1f; l2f]
                (mk_sequent
                   [mk_elem l1 d; mk_eq l1 l2; mk_eq (mk_read left l1) (mk_read right l2)]
                   [mk_eq mk_null (mk_read left l1)]);
            ],
      [di, mk_or [mk_and [mk_eq x mk_null; mk_eq d empty_loc]; 
                  mk_and [mk_neq x mk_null;
                          mk_not (mk_elem y d);                  
                          mk_forall ~ann:[Comment "in tree domain1"] [l1f] 
                            (mk_sequent [mk_elem l1 d] [mk_reach parent l1 x]);
                          mk_forall ~ann:[Comment "in tree domain2"] [l1f; l2f] 
                            (mk_sequent 
                               [mk_elem l1 d; mk_btwn parent l1 l2 x]
                               [mk_eq l1 l2;
                                mk_btwn parent l1 (mk_read left l2) l2; 
                                mk_btwn parent l1 (mk_read right l2) l2]);
                          (let ep_generator =
                            [TermGenerator 
                              ([l1f],
                               [],
                               [Match (l1, FilterNotOccurs EntPnt)],
                               mk_read left (mk_ep parent d l1));
                             TermGenerator 
                              ([l1f],
                               [],
                               [Match (mk_elem_term l1 s, FilterNotOccurs EntPnt)],
                               mk_read right (mk_ep parent d l1))
                           ] 
                          in
                          mk_forall ~ann:(Comment "not in tree domain" :: ep_generator) [l1f; l2f]
                            (mk_sequent 
                               [mk_eq l2 (mk_ep parent d l1)]
                               [mk_and [mk_neq l2 l1;
                                        mk_btwn parent l1 l2 x;
                                        mk_not (mk_reach parent l1 (mk_read left l2));
                                        mk_not (mk_reach parent l1 (mk_read right l2))];
                                mk_elem l1 d;
                                mk_not (mk_reach parent l1 x)]
                            ));
                          (*mk_forall ~ann:[Comment "not in tree domain2"] [l1f; l2f]
                            (mk_sequent 
                               [mk_btwn parent l1 l2 x; mk_or [mk_btwn parent l1 (mk_read left l2) l2;
                                                               mk_btwn parent l1 (mk_read right l2) l2]]
                               [mk_elem l1 d])*)
                        ]
                ]
     ]
     ) (* end of "tree" *)
     *)
  ]
  
let lists = [
    ( mk_ident "lseg",
      [df; nextf; xf; yf],
      mk_reach next x y,
      [di, mk_forall ~ann:[Comment "lseg_footprint"] [l1f] (mk_iff l1_in_domain l1_in_lst_fp)]);
    ( mk_ident "slseg",
      [df; dataf; nextf; xf; yf],
      mk_and [mk_reach next x y;
              mk_forall [l1f; l2f] (mk_implies (mk_and [l1_in_domain; l2_in_domain; mk_btwn next l1 l2 y])
                                               (mk_leq (mk_read data l1) (mk_read data l2)))],
      [di, mk_forall ~ann:[Comment "slseg_footprint"] [l1f] (mk_iff l1_in_domain l1_in_lst_fp)]);
    ( mk_ident "rslseg",
      [df; dataf; nextf; xf; yf],
      mk_and [mk_reach next x y;
              mk_forall [l1f; l2f] (mk_implies (mk_and [l1_in_domain; l2_in_domain; mk_btwn next l1 l2 y])
                                               (mk_leq (mk_read data l2) (mk_read data l1)))],
      [di, mk_forall ~ann:[Comment "rslseg_footprint"] [l1f] (mk_iff l1_in_domain l1_in_lst_fp)]);
    ( mk_ident "ulseg",
      [df; dataf; nextf; xf; yf; lbf],
      mk_and [mk_reach next x y;
              mk_forall [l1f] (mk_implies (l1_in_domain) (mk_leq lb (mk_read data l1)))],
      [di, mk_forall ~ann:[Comment "ulseg_footprint"] [l1f] (mk_iff l1_in_domain l1_in_lst_fp)]);
    ( mk_ident "llseg",
      [df; dataf; nextf; xf; yf; ubf],
      mk_and [mk_reach next x y;
              mk_forall [l1f] (mk_implies (l1_in_domain) (mk_leq (mk_read data l1) ub))],
      [di, mk_forall ~ann:[Comment "llseg_footprint"] [l1f] (mk_iff l1_in_domain l1_in_lst_fp)]);
    ( mk_ident "uslseg",
      [df; dataf; nextf; xf; yf; lbf],
      mk_and [mk_reach next x y;
              mk_forall [l1f] (mk_implies (l1_in_domain) (mk_leq lb (mk_read data l1)));
              mk_forall [l1f; l2f] (mk_implies (mk_and [l1_in_domain; l2_in_domain; mk_btwn next l1 l2 y])
                                               (mk_leq (mk_read data l2) (mk_read data l1)))],
      [di, mk_forall ~ann:[Comment "uslseg_footprint"] [l1f] (mk_iff l1_in_domain l1_in_lst_fp)]);
    ( mk_ident "lslseg",
      [df; dataf; nextf; xf; yf; ubf],
      mk_and [mk_reach next x y;
              mk_forall [l1f] (mk_implies (l1_in_domain) (mk_leq (mk_read data l1) ub));
              mk_forall [l1f; l2f] (mk_implies (mk_and [l1_in_domain; l2_in_domain; mk_btwn next l1 l2 y])
                                               (mk_leq (mk_read data l2) (mk_read data l1)))],
      [di, mk_forall ~ann:[Comment "lslseg_footprint"] [l1f] (mk_iff l1_in_domain l1_in_lst_fp)]);
    ( mk_ident "blseg",
      [df; dataf; nextf; xf; yf; lbf; ubf],
      mk_and [mk_reach next x y;
              mk_forall [l1f] (mk_implies (l1_in_domain) (mk_and [mk_leq (mk_read data l1) ub;
                                                                  mk_leq lb (mk_read data l1)]))],
      [di, mk_forall ~ann:[Comment "blseg_footprint"] [l1f] (mk_iff l1_in_domain l1_in_lst_fp)]);
    ( mk_ident "bslseg",
      [df; dataf; nextf; xf; yf; lbf; ubf],
      mk_and [mk_reach next x y;
              mk_forall [l1f] (mk_implies (l1_in_domain) (mk_and [mk_leq (mk_read data l1) ub;
                                                                  mk_leq lb (mk_read data l1)]));
              mk_forall [l1f; l2f] (mk_implies (mk_and [l1_in_domain; l2_in_domain; mk_btwn next l1 l2 y])
                                               (mk_leq (mk_read data l2) (mk_read data l1)))],
      [di, mk_forall ~ann:[Comment "bslseg_footprint"] [l1f] (mk_iff l1_in_domain l1_in_lst_fp)]);
    ( mk_ident "dlseg",
      [df; nextf; prevf; x1f; x2f; y1f; y2f],
      mk_and [mk_reach next x1 y1;
              mk_or [ mk_and [mk_eq x1 y1; mk_eq x2  y2];
                      mk_and [mk_eq (mk_read next y2) y1;
                              mk_eq (mk_read prev x1) x2;
                              mk_elem y2 d]];
              mk_forall [l1f;l2f]
                        (mk_sequent [mk_eq (mk_read next l1) l2; mk_elem l1 d; mk_elem l2 d]
                        [mk_eq (mk_read prev l2) l1])],
      [di, mk_forall ~ann:[Comment "dlseg_footprint"] [l1f] (mk_iff l1_in_domain (mk_and [mk_btwn next x1 l1 y1; mk_neq l1 y1]))]);
  ]


let with_fp = []
let with_content = []
let misc = []

(*
    "bdlseg(domain: set loc, data: fld int, next: fld loc, prev: fld loc, x1: loc, x2: loc, y1: loc, y2: loc, lb: int, ub:int){" ^
        "reach(next, x1, y1) &&" ^ 
        " ((x1 == y1 && x2 == y2) || (prev(x1) == x2 && next(y2) == y1 && y2 in domain)) &&"^
        (*" (forall l1: loc, l2: loc. (next(l1) == l2 && l1 in domain && l2 in domain) ==> prev(l2) == l1) &&"^*)
        " (forall l1: loc, l2: loc. (l1 in domain && l2 in domain) ==> (next(l1) == l2 <=> prev(l2) == l1)) &&"^
        " forall l1: loc. l1 in domain ==> (data(l1) >= lb && data(l1) <= ub)," ^
        "forall l1: loc. l1 in domain <=> (btwn(next, x1, l1, y1) && l1 != y1) }";
*)
(*
    "bsdlseg(domain: set loc, data: fld int, next: fld loc, prev: fld loc, x1: loc, x2: loc, y1: loc, y2: loc, lb: int, ub:int){" ^
        "reach(next, x1, y1) && ((x1 == y1 && x2 == y2) || (prev(x1) == x2 && next(y2) == y1 && y2 in domain)) && (forall l1: loc, l2: loc. (next(l1) == l2 && l1 in domain && l2 in domain) ==> prev(l2) == l1) && (forall l1: loc. l1 in domain ==> (data(l1) >= lb && data(l1) <= ub)) && forall l1: loc, l2: loc. (l1 in domain && l2 in domain && btwn(next, l1, l2, y)) ==> data(l1) <= data(l2)," ^
        "forall l1: loc. l1 in domain <=> (btwn(next, x1, l1, y1) && l1 != y1) }"
*)

(*
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

let symbols = without_fp @ lists @ with_fp @ with_content @ misc
