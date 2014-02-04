open Form
open FormUtil
open DefHelpers

let sorted = _sorted next y

let list_content = (
  ci, mk_and [mk_forall ~ann:[Comment "sorted_set_1"] [l1f]
               (mk_implies l1_in_lst_fp (mk_elem (mk_read data l1) c));
              mk_forall ~ann:[Comment "sorted_set_2"; witness_generator1; witness_generator2] [vf]
               (mk_and [mk_implies (mk_elem v c) (mk_and [mk_elem (mk_witness v c) d; mk_eq v (mk_read data (mk_witness v c))]);
                        mk_implies (mk_not (mk_elem v c)) (mk_eq (mk_witness v c) mk_null)])
             ])

let lists = [
    ( mk_ident "lseg",
      [df; nextf; xf; yf],
      mk_reach next x y,
      [di, mk_forall ~ann:[Comment "lseg_footprint"] [l1f] (mk_iff l1_in_domain l1_in_lst_fp)]);
    ( mk_ident "slseg",
      [df; dataf; nextf; xf; yf],
      mk_and [mk_reach next x y;
              sorted
             ],
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
              lower_bound],
      [di, mk_forall ~ann:[Comment "ulseg_footprint"] [l1f] (mk_iff l1_in_domain l1_in_lst_fp)]);
    ( mk_ident "llseg",
      [df; dataf; nextf; xf; yf; ubf],
      mk_and [mk_reach next x y;
              upper_bound],
      [di, mk_forall ~ann:[Comment "llseg_footprint"] [l1f] (mk_iff l1_in_domain l1_in_lst_fp)]);
    ( mk_ident "uslseg",
      [df; dataf; nextf; xf; yf; lbf],
      mk_and [mk_reach next x y;
              lower_bound;
              sorted],
      [di, mk_forall ~ann:[Comment "uslseg_footprint"] [l1f] (mk_iff l1_in_domain l1_in_lst_fp)]);
    ( mk_ident "lslseg",
      [df; dataf; nextf; xf; yf; ubf],
      mk_and [mk_reach next x y;
              upper_bound;
              sorted],
      [di, mk_forall ~ann:[Comment "lslseg_footprint"] [l1f] (mk_iff l1_in_domain l1_in_lst_fp)]);
    ( mk_ident "lrslseg",
      [df; dataf; nextf; xf; yf; ubf],
      mk_and [mk_reach next x y;
              upper_bound;
              mk_forall [l1f; l2f] (mk_implies (mk_and [l1_in_domain; l2_in_domain; mk_btwn next l1 l2 y])
                                               (mk_leq (mk_read data l2) (mk_read data l1)))],
      [di, mk_forall ~ann:[Comment "lrslseg_footprint"] [l1f] (mk_iff l1_in_domain l1_in_lst_fp)]);
    ( mk_ident "blseg",
      [df; dataf; nextf; xf; yf; lbf; ubf],
      mk_and [mk_reach next x y;
              bounded],
      [di, mk_forall ~ann:[Comment "blseg_footprint"] [l1f] (mk_iff l1_in_domain l1_in_lst_fp)]);
    ( mk_ident "bslseg",
      [df; dataf; nextf; xf; yf; lbf; ubf],
      mk_and [mk_reach next x y;
              bounded;
              sorted],
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


let with_fp = [
    ( mk_ident "lseg_set",
      [df; nextf; xf; yf; sf],
      mk_reach next x y,
      [di, mk_forall ~ann:[Comment "lseg_set_footprint"] [l1f] (mk_iff l1_in_domain l1_in_lst_fp);
       si, mk_forall ~ann:[Comment "lseg_Set"] [l1f] (mk_iff (mk_elem l1 s) l1_in_lst_fp)])
  ]

let with_content = [
  ( mk_ident "sorted_set_lb",
    [df; dataf; nextf; xf; yf; lbf; cf],
    mk_and [mk_reach next x y;
            lower_bound
            mk_forall ~ann:[Comment "strict_sortedness"] [l1f; l2f]
              (mk_sequent [l1_in_domain; l2_in_domain; mk_btwn next l1 l2 y; mk_neq l1 l2]
                 [mk_lt (mk_read data l1) (mk_read data l2)])
          ],
    [di, mk_forall ~ann:[Comment "sorted_set_footprint"] [l1f] (mk_iff l1_in_domain l1_in_lst_fp);
     list_content
   ]);
  ( mk_ident "sorted_set",
    [df; dataf; nextf; xf; yf; cf],
    mk_and [mk_reach next x y;
            mk_forall ~ann:[Comment "strict_sortedness"] [l1f; l2f]
              (mk_sequent [l1_in_domain; l2_in_domain; mk_btwn next l1 l2 y; mk_neq l1 l2]
                 [mk_lt (mk_read data l1) (mk_read data l2)])
          ],
    [di, mk_forall ~ann:[Comment "sorted_set_footprint"] [l1f] (mk_iff l1_in_domain l1_in_lst_fp);
     list_content
   ]);
  ( mk_ident "sorted_set2",
    [df; dataf; nextf; parentf; xf; yf; cf],
    mk_and [mk_reach next x y;
            mk_forall ~ann:[Comment "strict_sortedness"] [l1f; l2f]
              (mk_sequent [l1_in_domain; l2_in_domain; mk_btwn next l1 l2 y; mk_neq l1 l2]
                          [mk_lt (mk_read data l1) (mk_read data l2)]);
            mk_forall [l1f]
              (mk_implies l1_in_domain (mk_btwn parent l1 mk_null mk_null));
            mk_forall [l1f; l2f]
              (mk_sequent [l1_in_domain; mk_not (mk_eq l2 l1); mk_not (mk_eq l2 mk_null)]
                          [mk_not (mk_btwn parent l1 l2 mk_null)]);
          ],
    [di, mk_forall ~ann:[Comment "sorted_set_footprint"] [l1f] (mk_iff l1_in_domain l1_in_lst_fp);
     list_content
   ])
]

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
