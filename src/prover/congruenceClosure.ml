(** DZ: this is a copy-pasted version from csisat, just adaped to the current types *)

open Grass

(** Ordered sets represented as lists.
 * This module is inspired from the Sicstus/SWI prolog library with the same name.
 *)
  
module OrdSet =
  struct
    let remove_duplicates lst =
      let rec process last acc lst = match lst with
        | x::xs ->
          begin
            if x <> last then process x (x::acc) xs
            else process last acc xs
          end
        | [] -> List.rev acc
      in
        match lst with
        | x::[] -> [x]
        | x::xs -> process x [x] xs
        | [] -> []

    let subtract a b =
      let rec process acc a b = match (a,b) with
        | (a,[]) -> (List.rev acc)@a
        | ([],_) -> (List.rev acc)
        | (a::sa, b::bs) ->
          begin
            if a < b then process (a::acc) sa (b::bs)
            else if a > b then process acc (a::sa) bs
            else process acc sa (b::bs)
          end
      in
        process [] a b

    let union a b =
      let rec process acc a b = match (a,b) with
        | (a,[]) -> (List.rev acc)@a
        | ([],b) -> (List.rev acc)@b
        | (a::sa, b::bs) ->
          begin
            if a < b then process (a::acc) sa (b::bs)
            else if a > b then process (b::acc) (a::sa) bs
            else process (a::acc) sa bs
          end
      in
        process [] a b

    let intersection a b =
      let rec process acc a b = match (a,b) with
        | (_,[]) -> (List.rev acc)
        | ([],_) -> (List.rev acc)
        | (a::sa, b::bs) ->
          begin
            if a < b then process acc sa (b::bs)
            else if a > b then process acc (a::sa) bs
            else process (a::acc) sa bs
          end
      in
        process [] a b

    let rec mem el lst = match lst with
      | [] -> false
      | x::xs ->
        begin
            if x < el then mem el xs
            else if x > el then  false
            else true
        end

    let list_to_ordSet lst = remove_duplicates (List.sort compare lst)
  end


class node = 
  fun
    (ffname: symbol) 
    (aargs: node list) -> 
  object (self)
    val fname = ffname
    method get_fname = fname
    
    val args = aargs
    method get_args = args
    
    val arity = List.length aargs
    method get_arity = arity
    
    val mutable ccparent: node list = []
    method set_ccparent lst = ccparent <- lst
    method add_ccparent n = ccparent <- (OrdSet.union ccparent [n])
    method get_ccparent = ccparent
    
    val mutable parent: node option = None
    method set_parent n = parent <- Some n
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
        n2#set_ccparent (OrdSet.union n1#get_ccparent n2#get_ccparent);
        n1#set_ccparent []

    method ccpar: node list = (self#find)#get_ccparent

    method congruent (that: node) =
        self#get_fname = that#get_fname
      &&
        self#get_arity = that#get_arity
      &&
        List.for_all (fun (a,b) -> a#find = b#find) (List.rev_map2 (fun x y -> (x,y)) (self#get_args) (that#get_args))

    (** return pairs of nodes whose equality may change the result of the 'congruent' method*)
    method may_be_congruent (that: node) =
      if self#get_fname <> that#get_fname
      || self#get_arity <> that#get_arity
      || self#find = that#find then []
      else
        List.filter (fun (a,b) -> a#find <> b#find) (List.rev_map2 (fun x y -> (x,y)) (self#get_args) (that#get_args))

    method merge (that: node) =
      if self#find <> that#find then
        begin
          let p1 = self#ccpar in
          let p2 = that#ccpar in
            self#union that;
            let to_test =
              List.flatten (List.map (fun x -> List.map (fun y -> (x,y)) p2) p1)
            in
              List.iter (fun (x,y) -> if x#find <> y#find && x#congruent y then x#merge y) to_test
        end
    
    (** return pairs of nodes whose equality comes from congruence*)
    method merge_with_applied (that: node) =
      if self#find <> that#find then
        begin
          let p1 = self#ccpar in
          let p2 = that#ccpar in
            self#union that;
            let to_test = 
              List.flatten (List.map (fun x -> List.map (fun y -> (x,y)) p2) p1)
            in
              let cong = List.filter (fun (x,y) -> x#find <> y#find && x#congruent y) to_test in
                List.fold_left
                  (fun acc (x,y) -> if x#find <> y#find then
                    (x#merge_with_applied y) @ ((x,y)::acc)
                  else 
                    acc) [] cong
        end
      else []
  end

class dag = fun expr ->
  let table1 = Hashtbl.create 53 in
  let table2 = Hashtbl.create 53 in
  let create_and_add expr fn args =
    try Hashtbl.find table1 expr
    with Not_found ->
      begin
        let n = new node fn args
        in
          Hashtbl.replace table1 expr n;
          Hashtbl.replace table2 n expr;
          n
      end
  in
  let rec convert_exp expr =
    (*print_endline ("CC adding: " ^ (string_of_term expr));*)
    match expr with
    | Var (v, _) -> failwith "CC: term not ground" (* create_and_add var (FreeSym v) []*)
    | App (c, [], _) as cst -> create_and_add cst c [] (* TODO: redundant? *)
    | App (f, args, _) as appl ->
      let node_args = (List.map convert_exp args) in
      let new_node  = create_and_add appl f node_args in
        List.iter (fun n -> n#add_ccparent new_node) node_args;
        new_node
  in
  let _ = List.iter (fun x -> ignore (convert_exp x)) expr in
  object (self)
    val mutable neqs: (node * node) list = []
    val nodes: (term, node) Hashtbl.t = table1
    val node_to_expr: (node, term) Hashtbl.t = table2
    method get_node expr =
      try Hashtbl.find nodes expr
      with Not_found -> failwith ("CC: cannot find " ^ (string_of_term expr))
    method get_expr n = Hashtbl.find node_to_expr n
    method get_nodes = Hashtbl.copy nodes

    method print =
      let buffer = Buffer.create 1000 in
      let print_node (n:node) =
        Buffer.add_string buffer ("node: "^(string_of_term (self#get_expr n)));
        Buffer.add_char buffer '\n';
        Buffer.add_string buffer ("  in class of:  "^(string_of_term (self#get_expr n#find)));
        Buffer.add_char buffer '\n';
        Buffer.add_string buffer ("  ccparent are: "^(String.concat ", " (List.map (fun x -> string_of_term (self#get_expr x)) n#get_ccparent)));
        Buffer.add_char buffer '\n';
        Buffer.add_string buffer ("  ccpar    are: "^(String.concat ", " (List.map (fun x -> string_of_term (self#get_expr x)) n#ccpar)));
        Buffer.add_char buffer '\n';
      in
        Hashtbl.iter (fun _ n -> print_node n) nodes;
        Buffer.contents buffer

    method add_eq e1 e2 = 
      let n1 = self#get_node e1 in
      let n2 = self#get_node e2 in
      n1#merge n2

    method add_neq e1 e2 = 
      let n1 = self#get_node e1 in
      let n2 = self#get_node e2 in
      neqs <- (n1,n2) :: neqs

    method entails_eq e1 e2 =
      let n1 = self#get_node e1 in
      let n2 = self#get_node e2 in
      n1#find = n2#find
      
    method entails_neq e1 e2 =
      let n1 = (self#get_node e1)#find in
      let n2 = (self#get_node e2)#find in
      List.exists
        (fun (a,b) -> (a#find = n1 && b#find = n2) ||
                      (a#find = n2 && b#find = n1) )
        neqs
      

    (** Returns a method that maps a term to its representative *)
    method get_repr = (fun e -> self#get_expr (self#get_node e)#find)

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
      let repr = self#get_expr in
      let conflicts =
        List.fold_left
          (fun acc (e1,e2) ->
            let n1 = self#get_expr e1#find in
            let n2 = self#get_expr e2#find  in
            let c1 = try TermMap.find n1 acc with Not_found -> TermSet.empty in
            let c2 = try TermMap.find n2 acc with Not_found -> TermSet.empty in
            let c1p = TermSet.add n2 c1 in
            let c2p = TermSet.add n1 c2 in
            TermMap.add n2 c2p (TermMap.add n1 c1p acc))
          TermMap.empty
          neqs
      in
        (fun e1 e2 ->
          try TermSet.mem (repr e2) (TermMap.find (repr e1) conflicts)
          with Not_found -> false)

    method copy =
      let expressions = Hashtbl.fold (fun e _ acc -> e::acc ) nodes [] in
      let cp = new dag expressions in
      let new_of_old = Hashtbl.create (List.length expressions) in
        List.iter (fun e -> Hashtbl.add new_of_old (self#get_node e) (cp#get_node e) ) expressions;
        List.iter (fun e ->
          let new_node = cp#get_node e in
          let old_node = self#get_node e in 
            new_node#set_ccparent (List.map (Hashtbl.find new_of_old) (old_node#get_ccparent));
            let new_parent = Hashtbl.find new_of_old (old_node#find) in
              if new_parent <> new_node then new_node#set_parent new_parent
          ) expressions;
        cp

  end

  
(* TODO need implied equalities and watch lists *)
let congr_classes_fixed_point fs gts =
  let gterms = TermSet.add GrassUtil.mk_true_term (TermSet.add GrassUtil.mk_false_term gts) in
  let cc_graph = new dag (TermSet.elements gterms) in
  let rec remove_false1 f = match f with
    | Atom (App (Eq, [e1; e2], _), _) -> 
      if cc_graph#entails_neq e1 e2 then GrassUtil.mk_false else f
    | BoolOp (Not, [Atom (App (Eq, [e1; e2], _), _)])
    | Atom (App (Lt, [e1; e2], _), _) 
    | Atom (App (Gt, [e1; e2], _), _) ->
      if cc_graph#entails_eq e1 e2 then GrassUtil.mk_false else f
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
  let rec loop changed toProcess toSimplify = match toProcess with
    | f :: fs ->
      begin
        match remove_false f with
        | Binder (_, [], f, _) ->
          loop changed (f :: fs) toSimplify
        | BoolOp (And, fs1) ->
          loop changed (fs1 @ fs) toSimplify
        | Atom (App (Eq, [e1; e2], _), _) -> 
          cc_graph#add_eq e1 e2;
          loop true fs toSimplify
        | BoolOp (Not, [Atom (App (Eq, [e1; e2], _), _)])
        | Atom (App (Lt, [e1; e2], _), _) 
        | Atom (App (Gt, [e1; e2], _), _) ->
          cc_graph#add_neq e1 e2;
          loop true fs toSimplify
        | Atom (pred, _) ->
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
  (* Add disequalities between ADT terms with different top-level constructors *)
  let cterms =
    TermSet.filter
      (function App (Constructor _, _, _) -> true | _ -> false) gterms
  in
  TermSet.iter (function
    | App (Constructor id1, _, srt1) as t1 ->
        TermSet.iter (function
          | App (Constructor id2, _, srt2) as t2 when srt1 = srt2 && id1 <> id2 ->
              cc_graph#add_neq t1 t2
          | _ -> ())
          cterms
    | _ -> ()) cterms;
  (* Add disequality between true and false *)
  cc_graph#add_neq GrassUtil.mk_true_term GrassUtil.mk_false_term;
  (* Add top-level disequality unit clauses in fs *)
  loop false fs [];
  (* Compute congruence classes *)
  cc_graph#get_cc

let congr_classes_simple fs gterms =
  let cc_graph = new dag (TermSet.elements gterms) in
  let rec add = function
    | Binder (_, [], f, _) :: fs -> add (f :: fs)
    | BoolOp (And, fs1) :: fs -> add (fs1 @ fs)
    | Atom (App (Eq, [e1; e2], _), _) :: fs -> 
        cc_graph#add_eq e1 e2; add fs
    | BoolOp (Not, [Atom (App (Eq, [e1; e2], _), _)]) :: fs 
    | Atom (App (Lt, [e1; e2], _), _) :: fs
    | Atom (App (Gt, [e1; e2], _), _) :: fs ->
        cc_graph#add_neq e1 e2; add fs
    | _ :: fs -> add fs
    | [] -> ()
  in
  add fs;
  cc_graph#get_cc

let congr_classes fs gterms =
  if !Config.ccFixedPoint then
    congr_classes_fixed_point fs gterms
  else
    congr_classes_simple fs gterms

let class_of t classes = List.find (List.mem t) classes

let restrict_classes classes ts =
  List.filter (fun cc -> List.exists (fun t -> TermSet.mem t ts) cc) classes
