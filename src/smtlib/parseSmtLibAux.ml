open Form
open FormUtil

type smtlib_answer =
  | SmtSat
  | SmtUnsat
  | SmtUnknown
  | SmtForm of form
  | SmtModel of Model.model
  | SmtCore of string list
  | SmtError of string

let form_defs : (ident, form) Hashtbl.t = Hashtbl.create 0
let term_defs : (ident, term) Hashtbl.t = Hashtbl.create 0

let clear_tables () =
  Hashtbl.clear form_defs;
  Hashtbl.clear term_defs

let add_def id ft = 
  (match fst ft with
  | Some f -> Hashtbl.add form_defs id f
  | _ -> ());
  match snd ft with
  | Some t -> Hashtbl.add term_defs id t
  | _ -> ()

let resolve_id_to_term id =
  try Hashtbl.find term_defs id 
  with Not_found -> mk_free_const id

let resolve_id_to_form id =
  try Hashtbl.find form_defs id
  with Not_found -> mk_pred id []
