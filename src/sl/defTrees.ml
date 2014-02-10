open Form
open FormUtil
open DefHelpers

(* generators *)
let parent_generator child =
  TermGenerator ( [l1f], [],
                  [Match (mk_read child l1, FilterTrue)],
                  mk_read parent (mk_read child l1))
let left_generator =
  TermGenerator ( [l1f], [],
                  [Match (mk_read right l1, FilterTrue)],
                  mk_read left l1)
let right_generator =
  TermGenerator ( [l1f], [],
                  [Match (mk_read left l1, FilterTrue)],
                  mk_read right l1)
let data_generator =
  TermGenerator ( [l1f], [],
                  [Match (mk_read left l1, FilterTrue)],
                  mk_read data l1)

(* shorthands for strucutral constraints *)
let parent_equal child =
  (*mk_forall ~ann:[Comment ((string_of_term child)^"_parent_equal"); parent_generator child] [l1f] 
    (mk_sequent [mk_elem l1 d]
                [mk_eq (mk_read child l1) mk_null; mk_eq (mk_read parent (mk_read child l1)) l1])*)
  mk_and [mk_forall ~ann:[Comment ((string_of_term child)^"_parent_equal_1")] [l1f]
            (mk_sequent [mk_elem l1 d]
               [mk_eq (mk_read child l1) mk_null; mk_and [mk_reach parent (mk_read child l1) l1; mk_neq (mk_read child l1) l1]]);
          mk_forall ~ann:[Comment ((string_of_term child)^"_parent_equal_2")] [l1f; l2f]
            (mk_sequent [mk_elem l1 d; mk_btwn parent (mk_read child l1) l2 l1]
               [mk_eq l2 l1; mk_eq l2 (mk_read child l1)])]

let left_right_distinct =
  mk_forall ~ann:([Comment "left_right_distinct"; left_generator; right_generator]) [l1f]
    (mk_sequent
       [mk_elem l1 d; mk_eq (mk_read left l1) (mk_read right l1)]
       [mk_eq mk_null (mk_read left l1)])

let tree_fp = (di, mk_forall ~ann:([Comment "tree_footprint"]) [l1f] (mk_iff l1_in_domain (mk_and [mk_btwn parent l1 x x; mk_neq x mk_null])))

let tree_structure = [
    parent_equal left;
    parent_equal right;
    left_right_distinct;
    reach_via_left_right
  ]

let tree_sorted = [
    (*left is smaller, right is bigger*)
    mk_forall ~ann:[Comment "sorted_left"; data_generator] [l1f; l2f]
      (mk_sequent [l1_in_domain; l2_in_domain; mk_btwn parent l1 (mk_read left l2) l2]
                  [mk_lt (mk_read data l1) (mk_read data l2)]);
    mk_forall ~ann:[Comment "sorted_right"] [l1f; l2f]
      (mk_sequent [l1_in_domain; l2_in_domain; mk_btwn parent l1 (mk_read right l2) l2]
                  [mk_gt (mk_read data l1) (mk_read data l2)])
  ]

(*color for red-black tree*)
let _, redf, red = mk_formal_and_var "red" (Fld Bool)
let _, colorf, color = mk_formal_and_var "color" (Fld Int)
let red_generator =
  TermGenerator ( [l1f], [],
                  [Match (mk_read left l1, FilterTrue)],
                  mk_read red l1)
let color_generator =
  TermGenerator ( [l1f], [],
                  [Match (mk_read left l1, FilterTrue)],
                  mk_read color l1)
(*
let tree_rb_top = [
    mk_forall ~ann:[Comment "root_is_black"] [l1f]
      (mk_sequent [l1_in_domain; mk_eq (mk_read parent l1) mk_null]
                  [mk_not (mk_read_form red l1)]);
  ]
*)
let tree_rb = [
    mk_forall ~ann:[Comment "red_node_has_black_left_child"; red_generator] [l1f]
      (mk_sequent [l1_in_domain; mk_read_form red l1]
                  [mk_not (mk_read_form red (mk_read left l1)); mk_eq (mk_read left l1) mk_null]);
    mk_forall ~ann:[Comment "red_node_has_black_right_child"] [l1f]
      (mk_sequent [l1_in_domain; mk_read_form red l1]
                  [mk_not (mk_read_form red (mk_read left l1)); mk_eq (mk_read right l1) mk_null]);
    mk_forall ~ann:[Comment "black_node_number_of_child_1"] [l1f] (*implied by the invariant on number of black nodes on a path*)
      (mk_sequent [l1_in_domain; mk_not (mk_read_form red l1)]
                  [mk_and [mk_eq (mk_read left l1) mk_null; mk_eq (mk_read right l1) mk_null]; (*no child*)
                   mk_and [mk_neq (mk_read left l1) mk_null; mk_read_form red (mk_read left l1)]; (*red child on the left*)
                   mk_and [mk_neq (mk_read left l1) mk_null; mk_neq (mk_read left l1) mk_null;
                           mk_not (mk_read_form red (mk_read left l1));
                           mk_not (mk_read_form red (mk_read right l1))]; (* two black child *)
                   ]);
    (* TODO #black nodes on any path between the root and a leaf is the same*)
  ]
let tree_llrb_2_3_4 = [
    mk_forall ~ann:[Comment "left_leaning"] [l1f]
      (mk_sequent [l1_in_domain; mk_read_form red (mk_read right l1); mk_neq (mk_read right l1) mk_null]
                  [mk_and [mk_neq (mk_read left l1) mk_null; (mk_read_form red (mk_read left l1))]]);
  ]
let tree_llrb_2_3 = [
    mk_forall ~ann:[Comment "2_3_nodes_only"] [l1f]
      (mk_sequent [l1_in_domain; mk_neq (mk_read right l1) mk_null]
                  [mk_not (mk_read_form red (mk_read right l1))]);
  ]

let is_red l = mk_eq (mk_read color l) (FormUtil.mk_int 1)
let is_black l = mk_eq (mk_read color l) (FormUtil.mk_int 0)
let tree_rb_int = [
    mk_forall ~ann:[Comment "red_node_has_black_left_child"; color_generator] [l1f]
      (mk_sequent [l1_in_domain; is_red l1]
                  [is_black (mk_read left l1); mk_eq (mk_read left l1) mk_null]);
    mk_forall ~ann:[Comment "red_node_has_black_right_child"] [l1f]
      (mk_sequent [l1_in_domain; is_red l1]
                  [is_black (mk_read left l1); mk_eq (mk_read right l1) mk_null]);
    mk_forall ~ann:[Comment "black_node_number_of_child_1"] [l1f] (*implied by the invariant on number of black nodes on a path*)
      (mk_sequent [l1_in_domain; is_black l1] (*need is black ?*)
                  [mk_and [mk_eq (mk_read left l1) mk_null; mk_eq (mk_read right l1) mk_null]; (*no child*)
                   mk_and [mk_neq (mk_read left l1) mk_null; is_red (mk_read left l1)]; (*red child on the left*)
                   mk_and [mk_neq (mk_read left l1) mk_null; mk_neq (mk_read left l1) mk_null;
                           is_black (mk_read left l1);
                           is_black (mk_read right l1)]; (* two black child *)
                   ]);
    (* TODO #black nodes on any path between the root and a leaf is the same*)
  ]
let tree_llrb_2_3_4_int = [
    mk_forall ~ann:[Comment "left_leaning"] [l1f]
      (mk_sequent [l1_in_domain; is_red (mk_read right l1); mk_neq (mk_read right l1) mk_null]
                  [mk_and [mk_neq (mk_read left l1) mk_null; is_red (mk_read left l1)]]);
  ]
let tree_llrb_2_3_int = [
    mk_forall ~ann:[Comment "2_3_nodes_only"] [l1f]
      (mk_sequent [l1_in_domain; mk_neq (mk_read right l1) mk_null]
                  [is_black (mk_read right l1)]);
  ]

let fpi, fpf, fp = mk_formal_and_var "fp" (Set Loc)

(* definitions *)
let trees = [
    ( mk_ident "treeAllocInvariant",
      [df; parentf; sf],
      mk_and [
              mk_forall ~ann:([Comment "parent_eventually_null"]) [l1f]
                (mk_reach parent l1 mk_null);
              mk_forall ~ann:([Comment "parent_outside_null"]) [l1f; l2f]
                (mk_sequent
                   [mk_reach parent l1 l2]
                   [mk_eq l1 l2; mk_and [mk_elem l1 s; mk_elem l2 s]; mk_eq l2 mk_null]);
              ],
      [di, mk_eq d empty_loc]);
    (*( mk_ident "accTree",
      [df; parentf; xf],
      mk_and [],
      [di, mk_eq d (mk_enum [x])]);*)
    ( mk_ident "tree",
      [df; leftf; parentf; rightf; xf],
      mk_and tree_structure,
      [tree_fp]);
    ( mk_ident "heap",
      [df; dataf; leftf; parentf; rightf; xf],
      mk_and ((_sorted parent mk_null (*children are smaller than parent*)) :: tree_structure),
      [tree_fp]);
    (*
    ( mk_ident "bheap",
      [df; dataf; leftf; parentf; rightf; xf; yf; ubf],
      mk_and ((_sorted parent y (*children are smaller than parent*)) ::
              upper_bound ::
              tree_structure),
      [tree_fp]);
    *)
    ( mk_ident "bstree",
      [df; dataf; leftf; parentf; rightf; xf; lbf; ubf],
      mk_and (bounded :: tree_sorted @ tree_structure),
      [tree_fp]);
    ( mk_ident "stree",
      [df; dataf; leftf; parentf; rightf; xf; cf],
      mk_and (tree_sorted @ tree_structure),
      [tree_fp; set_content]);
    ( mk_ident "bstree_cnt",
      [df; dataf; leftf; parentf; rightf; xf; lbf; ubf; cf],
      mk_and (bounded :: tree_sorted @ tree_structure),
      [tree_fp; set_content ]);
    ( mk_ident "heap_cnt",
      [df; dataf; leftf; parentf; rightf; xf; cf],
      mk_and ((_sorted parent mk_null (*children are smaller than parent*)) :: tree_structure),
      [tree_fp; content ]);
    ( mk_ident "tree_set",
      [df; parentf; xf; sf],
      mk_and [mk_eq (mk_read parent x) mk_null],
      [tree_fp; (si, mk_eq s d)]);
    ( mk_ident "rb",
      [df; leftf; parentf; redf; rightf; xf],
      mk_and (tree_rb @ tree_structure),
      [tree_fp]);
    ( mk_ident "llrb",
      [df; leftf; parentf; redf; rightf; xf],
      mk_and (tree_rb @ tree_llrb_2_3_4 @ tree_structure),
      [tree_fp]);
    ( mk_ident "llrb23",
      [df; leftf; parentf; redf; rightf; xf],
      mk_and (tree_rb @ tree_llrb_2_3 @ tree_structure),
      [tree_fp]);
    ( mk_ident "rb_int",
      [df; colorf; leftf; parentf; rightf; xf],
      mk_and (tree_rb_int @ tree_structure),
      [tree_fp]);
    ( mk_ident "llrb_int",
      [df; colorf; leftf; parentf; rightf; xf],
      mk_and (tree_rb_int @ tree_llrb_2_3_4_int @ tree_structure),
      [tree_fp]);
    ( mk_ident "llrb23_int",
      [df; colorf; leftf; parentf; rightf; xf],
      mk_and (tree_rb_int @ tree_llrb_2_3_int @ tree_structure),
      [tree_fp]);
    ( mk_ident "stree2",
      [df; dataf; leftf; nextf; parentf; rightf; xf; cf],
      mk_and ((to_null next) @ tree_sorted @ tree_structure),
      [tree_fp; set_content]);
    ( mk_ident "stree2_b",
      [df; dataf; leftf; nextf; parentf; rightf; xf; lbf; ubf; cf],
      mk_and (bounded :: (to_null next) @ tree_sorted @ tree_structure),
      [tree_fp; set_content]);
  ]
