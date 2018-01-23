module type Vertex = sig
  type t

  val compare: t -> t -> int

  val hash: t -> int

  val equal: t -> t -> bool
end

module Make(V: Vertex)(VertexSet: Set.S with type elt = V.t): sig
  type t

  type vertex = V.t

  val empty: t

  val vertices: t -> VertexSet.t
      
  val add_vertex: t -> vertex -> t
      
  val add_edge: t -> vertex -> vertex -> t

  val add_edges: t -> vertex -> VertexSet.t -> t
      
  val topsort: t -> vertex list list
end
