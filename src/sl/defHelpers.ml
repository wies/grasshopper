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

let ci, cf, c = mk_formal_and_var "Content" (Set Int)
let isi, isf, is = mk_formal_and_var "I" (Set Int)


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

let _, vf, v = mk_int "v"

let empty_loc = mk_empty (Some (Set Loc))

(* short hand*)
let l1_in_domain = mk_elem l1 d
let l2_in_domain = mk_elem l2 d
let l1_in_lst_fp = mk_and [mk_btwn next x l1 y; mk_neq l1 y]

let _sorted next y (* data domain are fixed *) = 
  mk_forall ~ann:[Comment "sortedness"] [l1f; l2f]
    (mk_sequent [l1_in_domain; l2_in_domain; mk_btwn next l1 l2 y]
                [mk_leq (mk_read data l1) (mk_read data l2)])

let upper_bound = mk_forall [l1f] (mk_implies (l1_in_domain) (mk_leq (mk_read data l1) ub))
let lower_bound = mk_forall [l1f] (mk_implies (l1_in_domain) (mk_leq lb (mk_read data l1)))
let bounded = mk_forall [l1f] (mk_implies (l1_in_domain) (mk_and [mk_leq (mk_read data l1) ub;
                                                                  mk_leq lb (mk_read data l1)]))

(* witnesses for content *)
let witness_sym = FreeSym (mk_ident "witness")
let mk_witness elt set = mk_app ~srt:Loc witness_sym [data; elt; set] 

let witness_generator1 =
  TermGenerator
    ( [l1f], [],
      [Match (mk_read data l1, FilterNotOccurs witness_sym)],
      mk_read data (mk_witness (mk_read data l1) c))
let witness_generator2 =
  TermGenerator
    ( [vf], [isf],
      [Match (mk_elem_term v is, FilterNotOccurs witness_sym)],
      mk_read data (mk_witness v c))
let witness_generator3 =
  TermGenerator
    ( [vf], [isf],
      [Match (v, FilterNotOccurs witness_sym);
       (*Match (v, FilterNotOccurs Read)*)],
      mk_read data (mk_witness v c))
let witness_generator4 =
  TermGenerator
    ( [vf], [isf],
      [Match (v, FilterNotOccurs witness_sym)],
      mk_witness v c)
