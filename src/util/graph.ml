open Util

module type Vertex = sig
  type t

  val compare: t -> t -> int

  val hash: t -> int

  val equal: t -> t -> bool
end

module Make(V: Vertex)(VertexSet: Set.S with type elt = V.t) = struct

  type vertex = V.t

  module VertexMap = Map.Make(V)

  module H = Hashtbl.Make(V)
      
  type t = VertexSet.t * VertexSet.t VertexMap.t

  let vertices (vs, _) = vs
        
  let empty = (VertexSet.empty, VertexMap.empty)

  let add_vertex (vs, es) v = (VertexSet.add v vs, VertexMap.add v VertexSet.empty es)
      
  let add_edge (vs, es) src dst =
    (vs, VertexMap.update src (Opt.map (fun old_dsts -> VertexSet.add dst old_dsts)) es)

  let add_edges (vs, es) src dsts =
    (vs, VertexMap.update src (Opt.map (fun old_dsts -> VertexSet.union dsts old_dsts)) es)
       
  exception Found
      
  let mem s x =
    try
      Stack.iter (fun y -> if x = y then raise Found else ()) s;
      false
    with Found -> true

  let topsort (vs, es) =
    let index = ref 0 in
    let indexes = H.create 999 in
    let lowlinks = H.create 999 in
    let s = Stack.create () in
    
    let rec tarjan sccs v = 
      H.add indexes v !index;
      H.add lowlinks v !index;
      incr index;
      let succs = VertexMap.find v es in
      Stack.push v s;
      begin
        let sccs1 = VertexSet.fold
            (fun v' sccs ->
              if not (H.mem indexes v') then (
                let sccs1 = tarjan sccs v' in
                H.add lowlinks v (min (H.find lowlinks v) (H.find lowlinks v'));
                sccs1
               ) else begin 
                 if mem s v' then
                   H.add lowlinks v (min (H.find lowlinks v) (H.find indexes v'));
                 sccs
               end
            ) succs sccs
        in
        if H.find lowlinks v = H.find indexes v 
        then begin
          let rec loop acc = 
            let v' = Stack.pop s in
            if v = v' then v' :: acc
            else loop (v' :: acc)
          in
          (loop []) :: sccs1
        end
        else sccs1
      end
    in
    let sccs =
      VertexSet.fold
        (fun v sccs ->   
          if not (H.mem indexes v)
          then tarjan sccs v
          else sccs
        ) vs []
    in
    List.rev sccs
end
