open Form

type command =
  | DeclareFun of ident * arity
  | Assert of form
  | CheckSat
  | GetModel
  | Exit

let symbol_tbl : (symbol, arity) Hashtbl.t = Hashtbl.create 0
let bound_vars : (ident, term) Hashtbl.t = Hashtbl.create 0

let decl_bound_var id srt = Hashtbl.add bound_vars id (mk_var ~srt:srt id)
let remove_bound_var id = Hashtbl.remove bound_vars id
let decl_symbol id arity = Hashtbl.add symbol_tbl (FreeSym id) arity

let clear_tables () =
  Hashtbl.clear form_defs;
  Hashtbl.clear term_defs;
  Hashtbl.clear bound_vars;

let resolve_id_to_term id =
  try 
    Hashtbl.find term_defs id
  with Not_found ->
    try match Hashtbl.find symbol_tbl (FreeSym) id with
    | [], res_srt -> mk_free_const ~srt:res_srt id
    | _ -> failwith "number of expected arguments does not match for symbol " ^ (str_of_ident id)
    with Not_found -> failwith "unknown identifier: " ^ (str_of_ident id)

let get_arity_of_symbol id =
  try 
    Hashtbl.find symbol_tbl 
