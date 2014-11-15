open Util

type t = (Grass.ident StringMap.t) list

let empty = [StringMap.empty]

let push tbl = StringMap.empty :: tbl 

let pop tbl = List.tl tbl

let add tbl name id =
  StringMap.add name id (List.hd tbl) :: List.tl tbl

let declared_in_current tbl name =
  StringMap.mem name (List.hd tbl)

let find_local tbl name =
  match tbl with
  | [] -> None
  | t :: _ -> 
      try Some (StringMap.find name t)
      with Not_found -> None

let find tbl name =
  let rec find = function
    | [] -> None
    | t :: ts ->
        try Some (StringMap.find name t)
        with Not_found -> find ts
  in find tbl



