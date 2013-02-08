open Form
open FormUtil

let reduce_reachwo f =
  let reachwo_ax = Axioms.reachwo_axioms () in
  smk_and (f :: reachwo_ax)

let reduce f = reduce_reachwo f
