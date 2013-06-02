open Form
open FormUtil

type command =
  | DeclareFun of ident * arity
  | Assert of form
  | CheckSat
  | GetModel
  | Exit
  | Skip

let symbol_tbl : (symbol, arity) Hashtbl.t = Hashtbl.create 0
let bound_vars : (ident, term) Hashtbl.t = Hashtbl.create 0

let decl_bound_var id srt = Hashtbl.add bound_vars id (mk_var ~srt:srt id)
let remove_bound_var id = Hashtbl.remove bound_vars id
let decl_symbol sym arity = Hashtbl.add symbol_tbl sym arity

let clear_tables () =
  Hashtbl.clear bound_vars;
  Hashtbl.clear symbol_tbl

let resolve_id_to_term id =
  try Hashtbl.find bound_vars id
  with Not_found ->
    try match Hashtbl.find symbol_tbl (FreeSym id) with
    | [], res_srt -> mk_free_const ~srt:res_srt id
    | _ -> failwith ("wrong number of arguments for symbol " ^ (str_of_ident id))
    with Not_found -> failwith ("unknown identifier: " ^ (str_of_ident id))

let get_arity_of_symbol sym =
  try Hashtbl.find symbol_tbl sym
  with Not_found -> failwith ("unknown symbol: " ^ (str_of_symbol sym))

