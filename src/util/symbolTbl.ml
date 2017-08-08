open Util

type t = (Grass.ident Grass.IdMap.t) list

let empty = [Grass.IdMap.empty]

let push tbl = Grass.IdMap.empty :: tbl 

let pop tbl = List.tl tbl

let add tbl name id =
  Grass.IdMap.add name id (List.hd tbl) :: List.tl tbl

let remove tbl name =
  Grass.IdMap.remove name (List.hd tbl) :: List.tl tbl
                                          
let declared_in_current tbl name =
  Grass.IdMap.mem name (List.hd tbl)

let find_local tbl name =
  match tbl with
  | [] -> None
  | t :: _ -> 
      try Some (Grass.IdMap.find name t)
      with Not_found -> None

let find tbl name =
  let rec find = function
    | [] -> None
    | t :: ts ->
        try Some (Grass.IdMap.find name t)
        with Not_found -> find ts
  in find tbl



