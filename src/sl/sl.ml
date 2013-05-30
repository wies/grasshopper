
type ident = Form.ident
let mk_ident = FormUtil.mk_ident
module IdMap = Form.IdMap
module IdSet = Form.IdSet
let ident_to_string = Form.str_of_ident

(* the next pointer *)
let pts = mk_ident "next"
let prev_pts = mk_ident "prev"

let to_field f = FormUtil.mk_free_const ~srt:(Form.Fld Form.Loc) f

let fpts = to_field pts
let fprev_pts = to_field prev_pts

(* data pointer *)
let data = mk_ident "data"
let fdata = FormUtil.mk_free_const ~srt:(Form.Fld Form.Int) data
let get_data l = FormUtil.mk_read fdata l

type pred_symbol =
  | Emp
  | Cell
  | Pred of ident


type form =
  | Pure of Form.form
  (*| Spatial of symbol * Form.term list*)
  | Atom of pred_symbol * Form.term list
  | SepConj of form list
  | Not of form
  | And of form list
  | Or of form list

module SlSet = Set.Make(struct
    type t = form
    let compare = compare
  end)

module SlMap = Map.Make(struct
    type t = form
    let compare = compare
  end)

let rec to_string f = match f with
  | Pure p -> Form.string_of_form p
  | Not t -> "~(" ^ (to_string t) ^")"
  | And lst -> "(" ^ (String.concat ") && (" (List.map to_string lst)) ^ ")"
  | Or lst ->  "(" ^ (String.concat ") || (" (List.map to_string lst)) ^ ")"
  | Atom (Emp, _) -> "emp"
  | Atom (Cell, [t]) -> 
     Form.string_of_term t
  | Atom (Cell, _) -> failwith "Sl.to_string: expected one argument for Cell"
  | Atom (Pred p, ts) ->
      Form.str_of_ident p ^ "(" ^ String.concat ", " (List.map Form.string_of_term ts) ^ ")"
  (*
  | Spatial (p, [h; a; b]) when p.sym = "ptsTo" && h = fpts -> (Form.string_of_term a) ^ " |-> " ^ (Form.string_of_term b)
  | Spatial (p, [h; a; b]) when p.sym = "ptsTo" && h = fprev_pts -> (Form.string_of_term a) ^ " |<- " ^ (Form.string_of_term b)
  | Spatial (s, []) -> s.sym
  | Spatial (s, args) -> s.sym ^ "(" ^ (String.concat ", " (List.map Form.string_of_term args)) ^ ")"*)
  | SepConj fs -> "(" ^ (String.concat ") &*& (" (List.map to_string fs)) ^ ")"

