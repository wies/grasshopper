open Util
open Grass
open GrassUtil

let is_stratified t1 t2 =
    begin
    (*[ (Map (Loc, Bool), Bool);
        (Map (Loc, Loc), Loc);
        (Map (Loc, Int), Int);
        (Bool, Loc);
        (Loc, Int);
        (Loc, Set Loc);
        (Int, Set Int) ] *)
      match t1 with
      | Map (Loc _, (Bool | Loc _)) ->
        begin
          match t2 with
          | Bool | Loc _ | Int | Set Int | Set (Loc _) -> true
          | _ -> false
        end
      | Map (Loc _, Int) ->
        begin
          match t2 with
          | Bool | Int | Set Int -> true
          | _ -> false
        end
      | Loc _ ->
        begin
          match t2 with
          | Bool | Int | Set (Loc _) -> true
          | _ -> false
        end
      | Bool -> true
      | Int ->
        begin
          match t2 with
          | Bool | Set Int -> true
          | _ -> false
        end
      | _ -> t2 = Bool
    end

