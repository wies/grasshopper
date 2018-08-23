(** {5 Congruence closure computation} *)

open Util
open Grass
open GrassUtil
  
module rec Node : sig
  type t =
    < get_sym: symbol;
      get_args: t list;
      get_arity: int;
      set_ccparent: NodeSet.t -> unit;
      add_ccparent: t -> unit;
      get_ccparent: NodeSet.t;
      get_parent: t option;
      set_parent: t -> unit;
      find: t;
      union: t -> unit;
      ccpar: NodeSet.t;
      congruent: t -> bool;
      merge: t -> unit
    >

  val compare: t -> t -> int
  val create: symbol -> t list -> t
      
  end = struct
  type t =
    < get_sym: symbol;
      get_args: t list;
      get_arity: int;
      set_ccparent: NodeSet.t -> unit;
      add_ccparent: t -> unit;
      get_ccparent: NodeSet.t;
      get_parent: t option;
      set_parent: t -> unit;
      find: t;
      union: t -> unit;
      ccpar: NodeSet.t;
      congruent: t -> bool;
      merge: t -> unit
    >

  let compare = compare
        
  class node = 
  fun
    (sym: symbol) 
    (args: t list) -> 
  object (self)
    method get_sym = sym
    
    method get_args: node list = args
    
    val arity = List.length args
    method get_arity = arity
    
    val mutable ccparent = NodeSet.empty
    method set_ccparent lst = ccparent <- lst
    method add_ccparent (n: node) = ccparent <- (NodeSet.add n ccparent)
    method get_ccparent = ccparent
    
    val mutable parent: node option = None
    method get_parent: node option = parent
    method set_parent (n: node) = parent <- Some n
    method find: node = match parent with
      | None -> (self :> node)
      | Some n ->
        begin 
          let p = n#find in
            parent <- Some p;
            p
        end

    method union (that: node) = 
      let n1 = self#find in
      let n2 = that#find in
        n1#set_parent n2;
        n2#set_ccparent (NodeSet.union n1#get_ccparent n2#get_ccparent);
        n1#set_ccparent NodeSet.empty

    method ccpar: NodeSet.t = (self#find)#get_ccparent

    method congruent (that: node) =
        self#get_sym = that#get_sym
      &&
        self#get_arity = that#get_arity
      &&
        List.for_all2 (fun a b -> a#find = b#find) self#get_args that#get_args

    (** return pairs of nodes whose equality may change the result of the 'congruent' method*)
    (*method may_be_congruent (that: node) =
      if self#get_sym <> that#get_sym
      || self#get_arity <> that#get_arity
      || self#find = that#find then []
      else
        List.filter (fun (a,b) -> a#find <> b#find) (List.rev_map2 (fun x y -> (x,y)) (self#get_args) (that#get_args))*)

    method merge (that: node) =
      if self#find <> that#find then
        begin
          let p1 = self#ccpar in
          let p2 = that#ccpar in
          self#union that;
          NodeSet.iter (fun x ->
            NodeSet.iter
              (fun y -> if x#find <> y#find && x#congruent y then x#merge y)
              p2)
            p1
        end
  end

  let create sym terms: t = new node sym terms
  end
and NodeSet: Set.S with type elt = Node.t = Set.Make(Node)
        
class dag = fun (terms: TermSet.t) ->
  let table1 = Hashtbl.create 53 in
  let table2 = Hashtbl.create 53 in
  let create_and_add t sym args =
    try Hashtbl.find table1 t
    with Not_found ->
      begin
        let n = Node.create sym args
        in
          Hashtbl.add table1 t n;
          Hashtbl.add table2 n t;
          n
      end
  in
  let rec convert_term t =
    (*print_endline ("CC adding: " ^ (string_of_term t));*)
    match t with
    | Var (v, _) -> failwith "CC: term not ground" (* create_and_add var (FreeSym v) []*)
    | App (sym, args, _) as appl ->
      let node_args = List.map convert_term args in
      let new_node  = create_and_add appl sym node_args in
        List.iter (fun n -> n#add_ccparent new_node) node_args;
        new_node
  in
  let _ = TermSet.iter (fun t -> ignore (convert_term t)) terms in
  object (self)
    val mutable neqs: (Node.t * Node.t) list = []
    val nodes: (term, Node.t) Hashtbl.t = table1
    val node_to_term: (Node.t, term) Hashtbl.t = table2

    method get_node t =
      try Hashtbl.find nodes t
      with Not_found -> failwith ("CC: cannot find " ^ (string_of_term t))

    method get_term n = Hashtbl.find node_to_term n

    method get_terms = Hashtbl.fold (fun t _ acc -> TermSet.add t acc) nodes TermSet.empty
      
    method get_nodes = Hashtbl.copy nodes

    method print =
      let buffer = Buffer.create 1000 in
      let print_node (n: Node.t) =
        Buffer.add_string buffer ("node: "^(string_of_term (self#get_term n)));
        Buffer.add_char buffer '\n';
        Buffer.add_string buffer ("  in class of:  "^(string_of_term (self#get_term n#find)));
        Buffer.add_char buffer '\n';
        Buffer.add_string buffer ("  ccparent are: "^(String.concat ", " (List.map (fun x -> string_of_term (self#get_term x)) (NodeSet.elements n#get_ccparent))));
        Buffer.add_char buffer '\n';
        Buffer.add_string buffer ("  ccpar    are: "^(String.concat ", " (List.map (fun x -> string_of_term (self#get_term x)) (NodeSet.elements n#ccpar))));
        Buffer.add_char buffer '\n';
      in
        Hashtbl.iter (fun _ n -> print_node n) nodes;
        Buffer.contents buffer
 
    method add_term t =
      let n = convert_term t in
      let arg_opt = List.nth_opt n#get_args 0 in
      arg_opt |>
      Opt.iter (fun arg -> NodeSet.iter (fun n' -> if n' <> n && n#congruent n' then n#merge n') arg#ccpar)
       
    method add_eq t1 t2 = 
      let n1 = self#get_node t1 in
      let n2 = self#get_node t2 in
      n1#merge n2

    method add_neq t1 t2 = 
      let n1 = self#get_node t1 in
      let n2 = self#get_node t2 in
      neqs <- (n1,n2) :: neqs

    method entails_eq t1 t2 =
      let n1 = self#get_node t1 in
      let n2 = self#get_node t2 in
      n1#find = n2#find
      
    method entails_neq t1 t2 =
      let n1 = (self#get_node t1)#find in
      let n2 = (self#get_node t2)#find in
      List.exists
        (fun (a,b) -> (a#find = n1 && b#find = n2) ||
                      (a#find = n2 && b#find = n1) )
        neqs
      

    (** Returns a method that maps a term to its representative *)
    method get_repr = (fun t -> self#get_term (self#get_node t)#find)

    (** Gets a list of list of equal expressions (connected components). *)
    method get_cc =
      let node_to_cc = Hashtbl.create (Hashtbl.length nodes) in
        Hashtbl.iter (fun e n ->
            let parent = n#find in
            let already =
              try Hashtbl.find node_to_cc parent
              with Not_found -> []
            in
              Hashtbl.replace node_to_cc parent (e::already)
          ) nodes;
        Hashtbl.fold (fun _ cc acc -> cc::acc) node_to_cc []

    (* Returns a function that tests if two terms must be different *)
    method get_conflicts =
      let repr = self#get_term in
      let conflicts =
        List.fold_left
          (fun acc (t1, t2) ->
            let n1 = self#get_term t1#find in
            let n2 = self#get_term t2#find  in
            let c1 = try TermMap.find n1 acc with Not_found -> TermSet.empty in
            let c2 = try TermMap.find n2 acc with Not_found -> TermSet.empty in
            let c1p = TermSet.add n2 c1 in
            let c2p = TermSet.add n1 c2 in
            TermMap.add n2 c2p (TermMap.add n1 c1p acc))
          TermMap.empty
          neqs
      in
        (fun t1 t2 ->
          try TermSet.mem (repr t2) (TermMap.find (repr t1) conflicts)
          with Not_found -> false)

    method copy =
      let terms = self#get_terms in
      let cp = new dag terms in
      let new_of_old = Hashtbl.create (TermSet.cardinal terms) in
        TermSet.iter (fun t -> Hashtbl.add new_of_old (self#get_node t) (cp#get_node t) ) terms;
        TermSet.iter (fun t ->
          let new_node = cp#get_node t in
          let old_node = self#get_node t in 
            new_node#set_ccparent (NodeSet.fold (fun n acc -> NodeSet.add (Hashtbl.find new_of_old n) acc) (old_node#get_ccparent) NodeSet.empty);
            let new_parent = Hashtbl.find new_of_old (old_node#find) in
              if new_parent <> new_node then new_node#set_parent new_parent
          ) terms;
        cp

  end

  
(* TODO need implied equalities and watch lists *)
let add_conjuncts_fixed_point cc_graph fs : dag =
  let rec remove_false1 f = match f with
    | Atom (App (Eq, [t1; t2], _), _) -> 
      if cc_graph#entails_neq t1 t2 then GrassUtil.mk_false else f
    | BoolOp (Not, [Atom (App (Eq, [t1; t2], _), _)])
    | Atom (App (Lt, [t1; t2], _), _) 
    | Atom (App (Gt, [t1; t2], _), _) ->
      if cc_graph#entails_eq t1 t2 then GrassUtil.mk_false else f
    | Atom (App (Elem, [t1; t2], _) as pred, _) ->
        if cc_graph#entails_eq t2 (GrassUtil.mk_empty (sort_of t2)) then GrassUtil.mk_false else
        if cc_graph#entails_eq pred GrassUtil.mk_false_term then GrassUtil.mk_false else f
    | Atom (pred, _) ->
      if cc_graph#entails_eq pred GrassUtil.mk_false_term then GrassUtil.mk_false else f
    | BoolOp (Not, [Atom (pred, _)]) ->
      if cc_graph#entails_eq pred GrassUtil.mk_true_term then GrassUtil.mk_false else f
    | BoolOp (And, fs) ->
      GrassUtil.smk_and (List.map remove_false1 fs)
    | BoolOp (Or, fs) ->
        GrassUtil.smk_or (List.map remove_false1 fs)
    | other -> other
  in
  let remove_false f = match f with
    | BoolOp (Or, fs) ->
      let fs1 = List.map remove_false1 fs in
      GrassUtil.smk_or fs1
    | other -> other
  in
  let singletons = TermSet.filter (function App (SetEnum, [_], _) -> true | _ -> false) cc_graph#get_terms in
  let rec loop changed toProcess toSimplify = match toProcess with
    | f :: fs ->
      begin
        match remove_false f with
        | Binder (_, [], f, _) ->
          loop changed (f :: fs) toSimplify
        | BoolOp (And, fs1) ->
          loop changed (fs1 @ fs) toSimplify
        | Atom (App (Eq, [t1; t2], _), _) -> 
          cc_graph#add_eq t1 t2;
            loop true fs toSimplify
        | BoolOp (Not, [Atom (App (Eq, [t1; t2], _), _)])
        | Atom (App (Lt, [t1; t2], _), _) 
        | Atom (App (Gt, [t1; t2], _), _) ->
          cc_graph#add_neq t1 t2;
          loop true fs toSimplify
        | Atom (pred, _) ->
            let _ = match pred with
            | App (Elem, [t1; t2], _) ->
                TermSet.iter (function
                  | App (SetEnum, [t1'], _) as t2' when cc_graph#entails_eq t2 t2' ->
                      cc_graph#add_eq t1 t1'
                  | _ -> ())
                  singletons
            | _ -> ()
            in
            cc_graph#add_eq pred GrassUtil.mk_true_term;
            loop true fs toSimplify
        | BoolOp (Not, [Atom (pred, _)]) ->
          cc_graph#add_eq pred GrassUtil.mk_false_term;
          loop true fs toSimplify
        | BoolOp (Or, _) as f ->
          loop changed fs (f :: toSimplify)
        | _ -> loop changed fs toSimplify
      end
    | [] ->
      if changed then loop false toSimplify []
  in
  (* Add top-level disequality unit clauses in fs *)
  loop false fs [];
  cc_graph

let add_conjuncts_simple cc_graph fs : dag =
  let rec add = function
    | Binder (_, [], f, _) :: fs -> add (f :: fs)
    | BoolOp (And, fs1) :: fs -> add (fs1 @ fs)
    | Atom (App (Eq, [t1; t2], _), _) :: fs -> 
        cc_graph#add_eq t1 t2; add fs
    | BoolOp (Not, [Atom (App (Eq, [t1; t2], _), _)]) :: fs 
    | Atom (App (Lt, [t1; t2], _), _) :: fs
    | Atom (App (Gt, [t1; t2], _), _) :: fs ->
        cc_graph#add_neq t1 t2; add fs
    | _ :: fs -> add fs
    | [] -> ()
  in
  add fs;
  cc_graph

let add_conjuncts fs cc_graph : dag =
  if !Config.ccFixedPoint then
    add_conjuncts_fixed_point cc_graph fs 
  else
    add_conjuncts_simple cc_graph fs
      
let add_terms gterms cc_graph =
  let old_terms = cc_graph#get_terms in
  let new_terms = TermSet.diff gterms old_terms in
  let all_terms = TermSet.union old_terms new_terms in
  (* Add gterms to graph *)
  TermSet.iter (cc_graph#add_term) new_terms;
  (* Add disequalities between ADT terms with different top-level constructors *)
  let cterms =
    TermSet.filter
      (function App (Constructor _, _, _) -> true | _ -> false) new_terms
  in
  TermSet.iter (function
    | App (Constructor id1, _, srt1) as t1 ->
        TermSet.iter (function
          | App (Constructor id2, _, srt2) as t2 when srt1 = srt2 && id1 <> id2 ->
              cc_graph#add_neq t1 t2
          | _ -> ())
          all_terms
    | _ -> ()) cterms;
  cc_graph

let get_implied_equalities cc_graph =
  List.fold_left
    (fun acc -> function
      | c :: cls when sort_of c <> Bool && sort_of c <> Pat -> 
          let eq = List.map (fun t -> GrassUtil.mk_eq c t) cls in
          List.rev_append eq acc
            (*| c :: _ as cls when sort_of c = Bool ->
            let mk_form =
              if List.mem mk_true_term cls then
                function
                  | App (BoolConst _, _, _) -> []
                  | t -> [Atom (t, [])]
              else if List.mem mk_false_term cls then
                function
                  | App (BoolConst _, _, _) -> []
                  | t -> [mk_not (Atom (t, []))]
              else fun _ -> []
            in
              List.rev_append (flat_map mk_form cls) acc*)
      | _ -> acc)
    []
    cc_graph#get_cc
    
let create () : dag =
  let terms = TermSet.of_list [mk_true_term; mk_false_term] in
  let cc_graph = new dag terms in
  (* Add disequality between true and false *)
  cc_graph#add_neq mk_true_term mk_false_term;
  cc_graph

let get_classes cc_graph = cc_graph#get_cc
    
let congruence_classes fs =
  create () |>
  add_terms (ground_terms ~include_atoms:true (mk_and fs)) |>
  add_conjuncts fs |>
  get_classes
      
let class_of t classes = List.find (List.mem t) classes

let restrict_classes classes ts =
  List.filter (fun cc -> List.exists (fun t -> TermSet.mem t ts) cc) classes
