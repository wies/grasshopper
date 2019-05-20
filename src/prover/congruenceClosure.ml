(** {5 Congruence closure computation} *)

open Util
open Grass
open GrassUtil
  
module rec Node : sig
  type t =
    < get_id: int;
      get_sym: sorted_symbol;
      get_args: t list;
      get_arity: int;
      set_ccparent: NodeSet.t -> unit;
      add_ccparent: t -> unit;
      get_ccparent: NodeSet.t;
      get_parent: t option;
      set_parent: t -> unit;
      get_funs: sorted_symbol BloomFilter.t;
      set_funs: sorted_symbol BloomFilter.t -> unit;    
      find: t;
      union: t -> unit;
      ccpar: NodeSet.t;
      congruent: t -> bool;
      merge: t -> bool;
      to_term: term;
    >

  val compare: t -> t -> int
  val create: int -> sorted_symbol -> t list -> t
      
  end = struct
  type t =
    < get_id: int;
      get_sym: sorted_symbol;
      get_args: t list;
      get_arity: int;
      set_ccparent: NodeSet.t -> unit;
      add_ccparent: t -> unit;
      get_ccparent: NodeSet.t;
      get_parent: t option;
      set_parent: t -> unit;
      get_funs: sorted_symbol BloomFilter.t;
      set_funs: sorted_symbol BloomFilter.t -> unit;
      find: t;
      union: t -> unit;
      ccpar: NodeSet.t;
      congruent: t -> bool;
      merge: t -> bool;
      to_term: term
    >

  let compare n1 n2 = n1#get_id - n2#get_id
      
  class node = 
  fun
    (id: int)
    (sym: sorted_symbol) 
    (args: t list) -> 
  object (self)
    method get_id = id          
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

    val mutable funs: sorted_symbol BloomFilter.t =
      match args with
      | [] -> BloomFilter.empty
      | _ -> BloomFilter.singleton sym
      
    method get_funs: sorted_symbol BloomFilter.t = funs
    method set_funs symbols = funs <- symbols
            
    method union (that: node) = 
      let n1 = self#find in
      let n2 = that#find in
      let n1, n2 =
        if n1#get_arity <> 0 && n2#get_arity = 0
        then n1, n2
        else n2, n1
      in
      n1#set_parent n2;
      n2#set_ccparent (NodeSet.union n1#get_ccparent n2#get_ccparent);
      n1#set_ccparent NodeSet.empty;
      n2#set_funs (BloomFilter.union n1#get_funs n2#get_funs)

    method ccpar: NodeSet.t = (self#find)#get_ccparent

    method congruent (that: node) =
      (*print_endline "CC congruent %s %s" (string_of_term self#to_term) (string_of_term that#to_term);*)
        self#get_sym = that#get_sym
      &&
        List.for_all2 (fun a b -> a#find = b#find) self#get_args that#get_args

    (** return pairs of nodes whose equality may change the result of the 'congruent' method*)
    (*method may_be_congruent (that: node) =
      if self#get_sym <> that#get_sym
      || self#get_arity <> that#get_arity
      || self#find = that#find then []
      else
        List.filter (fun (a,b) -> a#find <> b#find) (List.rev_map2 (fun x y -> (x,y)) (self#get_args) (that#get_args))*)

    method to_term =
      let sym, (_, srt) = self#get_sym in
      mk_app srt sym (List.map (fun n -> n#to_term) args)
      
        
    method merge (that: node) =
      self#find != that#find &&
      begin
        (*Printf.printf "CC merging %s = %s\n" (string_of_term self#to_term) (string_of_term that#to_term);*)
        let p1 = self#ccpar in
        let p2 = that#ccpar in
        self#union that;
        NodeSet.iter (fun x ->
          NodeSet.iter
            (fun y -> if x#find != y#find && x#congruent y then ignore (x#merge y))
            p2)
          p1;
        true
      end
  end

  let create id sym terms: t = new node id sym terms
  end
and NodeSet: Set.S with type elt = Node.t = Set.Make(Node)


module NodeListSet =
  Set.Make(struct
    type t = Node.t list
    let compare = compare
  end)
    
module EGraphA =
  Map.Make(struct
    type t = Node.t * sorted_symbol
    let compare = compare
  end)

module EGraphP =
  Map.Make(struct
    type t = Node.t * sorted_symbol * int
    let compare = compare
  end)

type egraph = NodeListSet.t EGraphA.t * (NodeListSet.t * NodeSet.t) EGraphP.t
      
class dag = fun (terms: TermSet.t) ->
  let id_count = ref 0 in
  let table1 = Hashtbl.create 53 in
  let table2 = Hashtbl.create 53 in
  let create_and_add t sym args =
    try Hashtbl.find table1 t
    with Not_found ->
      begin
        let id = incr id_count; !id_count in
        let n = Node.create id sym args
        in
          Hashtbl.add table1 t n;
          Hashtbl.add table2 n t;
          n
      end
  in
  
  let rec convert_term t =
    (*print_endline ("CC adding: " ^ (string_of_term t));*)
    match t with
    | Var (v, _) -> failwith ("CC: term not ground " ^ string_of_term t) (* create_and_add var (FreeSym v) []*)
    | App (_, args, _) as appl ->
        let has_mod_args, node_args =
          List.fold_left (fun (has_mod_args, node_args) arg ->
            let has_mod, n = convert_term arg in
            has_mod || has_mod_args, n :: node_args)
            (false, []) args
        in
      let new_node  = create_and_add appl (sorted_symbol_of appl |> Opt.get) (List.rev node_args) in
      List.iter (fun n -> n#find#add_ccparent new_node) node_args;
      let has_mod = match new_node#get_args with
      | [] -> true
      | arg :: _ ->
          (*Printf.printf "Getting parents of %s\n" (string_of_term @@ arg#find#to_term);*)
          NodeSet.exists (fun n' ->
            (*Printf.printf "Checking congruence with: %s %b\n"
              (string_of_term @@ n'#to_term) (new_node#congruent n');*)
            n' != new_node && new_node#congruent n' && n'#merge new_node) arg#ccpar
      in
      has_mod_args || has_mod, new_node
  in

  let convert_term = measure_call "CC.convert_term" convert_term in
  
  let _ = TermSet.iter (fun t -> ignore (convert_term t)) terms in
  object (self)
    val mutable _has_mods: bool = true
    val mutable neqs: (Node.t * Node.t) list = []
    val nodes: (term, Node.t) Hashtbl.t = table1
    val node_to_term: (Node.t, term) Hashtbl.t = table2

    method has_mods = _has_mods

    method reset = _has_mods <- false
        
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
      (*Printf.printf "Adding term to cc: %s\n" (string_of_term t);*)
      let has_mod, n = convert_term t in
      _has_mods <- _has_mods || has_mod
        
    method add_eq t1 t2 =
      (*Printf.printf "CC adding equality %s\n" (string_of_term (mk_eq_term t1 t2));*)
      let n1 = self#get_node t1 in
      let n2 = self#get_node t2 in
      let has_mod =
        if size_of_term t1 > size_of_term t2
        then n2#merge n1
        else n1#merge n2
      in
      _has_mods <- _has_mods || has_mod 

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

    method get_reps =
        Hashtbl.fold
        (fun _ n reps -> NodeSet.add (n#find) reps)
        nodes NodeSet.empty
        
    (** Gets a list of list of equal expressions (connected components). *)
    method get_cc =
      let node_to_cc = Hashtbl.create (Hashtbl.length nodes) in
        Hashtbl.iter (fun e n ->
            let parent = n#find in
            let already =
              try Hashtbl.find node_to_cc parent
              with Not_found -> [Hashtbl.find node_to_term parent]
            in
            if n != parent then
              Hashtbl.replace node_to_cc parent (e::already)
          ) nodes;
        Hashtbl.fold (fun _ cc acc -> List.rev cc :: acc) node_to_cc []

    method get_egraph: egraph =
      let egraph = 
        Hashtbl.fold (fun _ n (egrapha, egraphp) -> 
          let n_rep = n#find in
          let arg_reps =
            List.map (fun n -> n#find) n#get_args
          in
          let other_args_reps =
            EGraphA.find_opt (n_rep, n#get_sym) egrapha |>
            Opt.get_or_else NodeListSet.empty
          in
          let egrapha' =
            EGraphA.add (n_rep, n#get_sym) (NodeListSet.add arg_reps other_args_reps) egrapha
          in
          let egraphp', _ =
            List.fold_left
              (fun (egraphp', k) arg_rep ->
                let other_args, other_parents =
                  EGraphP.find_opt (arg_rep, n#get_sym, k) egraphp' |>
                  Opt.get_or_else (NodeListSet.empty, NodeSet.empty)
                in
                let args' = NodeListSet.add arg_reps other_args in
                let parents' = NodeSet.add n_rep other_parents in
                EGraphP.add (arg_rep, n#get_sym, k) (args', parents') egraphp',
                k + 1)
              (egraphp, 0) arg_reps
          in
          egrapha', egraphp')
          nodes (EGraphA.empty, EGraphP.empty)
      in
      egraph
          
        
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

let print_classes cc_graph =
  ignore
    (List.fold_left (fun num cl ->
      print_endline ("Class " ^ string_of_int num ^ ": " ^ (string_of_sort (sort_of (List.hd cl))));
      List.iter (fun t -> print_endline ("    " ^ (string_of_term t))) cl; 
      print_newline ();
      num + 1) 1 (List.sort compare (cc_graph#get_cc)))
    
  
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
  (*Debug.debugl 1 (fun () -> "CC.add_terms: adding terms\n");*)
  TermSet.iter (fun t ->
    let st = SimplifyGrass.simplify_term t in
    cc_graph#add_term t;
    if st <> t then begin
      if not @@ TermSet.mem st old_terms then
        cc_graph#add_term st;
      cc_graph#add_eq st t  
      end)
    new_terms;
  (* Add disequalities between ADT terms with different top-level constructors *)
  (*Debug.debugl 1 (fun () -> "CC.add_terms: adding disequalities\n");*)
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
          cterms
    | App (Destructor did, [App (Constructor cid, args, Adt (adt, adts))], _) as t ->
        let cnstrs = List.assoc adt adts in
        let destrs = List.assoc cid cnstrs in
        List.combine destrs args |>
        List.find_opt (fun ((did', _), _) -> did = did') |>
        Opt.iter (fun (_, arg) -> cc_graph#add_eq t arg)
    | _ -> ()) all_terms;
  cc_graph

let get_implied_equalities cc_graph =
  let rec get_implied acc = function
    | (c :: cls) :: ccs when sort_of c <> Bool && sort_of c <> Pat ->
        let rec get_eq acc = function
          | t :: cls ->
              (match t, c with
              | App (IntConst i2, [], _), App (IntConst i1, [], _) when i1 <> i2 ->
                  [mk_false]
              | _ -> get_eq (mk_eq c t :: acc) cls)
          | [] -> get_implied acc ccs
        in
        get_eq acc cls
    | _ :: ccs -> get_implied acc ccs 
    | [] -> acc
  in
  get_implied [] cc_graph#get_cc
    
let create () : dag =
  let terms = TermSet.of_list [mk_true_term; mk_false_term] in
  let cc_graph = new dag terms in
  (* Add disequality between true and false *)
  cc_graph#add_neq mk_true_term mk_false_term;
  cc_graph

let rep_of_term cc_graph t = (cc_graph#get_node t)#find

let get_terms cc_graph = cc_graph#get_terms
    
let term_of_rep cc_graph n = cc_graph#get_term n

let funs_of_rep ccgraph n = n#get_funs
    
let get_egraph cc_graph = cc_graph#get_egraph
    
let get_classes cc_graph = cc_graph#get_cc

let get_reps cc_graph = cc_graph#get_reps
    
let congruence_classes gts fs =
  create () |>
  add_terms (ground_terms_acc ~include_atoms:true gts (mk_and fs)) |>
  add_conjuncts fs
      
let class_of t classes = List.find (List.mem t) classes

let find_rep ccgraph n = n#find

let has_mods ccgraph = ccgraph#has_mods

let reset ccgraph = ccgraph#reset; ccgraph
    
let restrict_classes classes ts =
  List.filter (fun cc -> List.exists (fun t -> TermSet.mem t ts) cc) classes

