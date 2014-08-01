open Form
open Sl

(* by convention domain should be the first arg *)

type symbol =
    { sym_name: ident;
      parameters: (ident * sort) list;
      structure: Form.form;
      outputs: (ident * Form.form) list;
      pos_only: Form.form option
    }

let symbols = Hashtbl.create 15

let get_symbol (s: ident) = Hashtbl.find symbols s
let put_symbol sym = Hashtbl.replace symbols sym.sym_name sym

let subst_id map_id s =
  let try_sub id = try IdMap.find id map_id with Not_found -> id in
    { sym_name = try_sub s.sym_name;
      parameters = List.map (fun (i, s) -> (try_sub i, s)) s.parameters;
      structure = FormUtil.subst_id map_id s.structure;
      outputs = List.map (fun (i,f) -> (try_sub i, FormUtil.subst_id map_id f)) s.outputs;
      pos_only = Util.Opt.map (FormUtil.subst_id map_id) s.pos_only
    }

let pred_struct (name, num) = (name ^ "_struct", num)
(*let pred_domain (name, num) = (name ^ "_domain", num)*)
let pred_naming (name, num) (p, _) = (name ^ "_" ^ p, num)

let make_output_fct sym id =
  let args =
    List.map
      (fun (i, s) -> FormUtil.mk_var s i)
      (List.filter
        (fun (i, _) -> List.for_all (fun (i2,_) -> i <> i2) sym.outputs)
        sym.parameters)
  in
  let srt = snd (List.find (fun (i,_) -> i = id) sym.parameters) in
    FormUtil.mk_free_fun srt (pred_naming sym.sym_name id) args

let pred_to_form p args =
  let def = get_symbol p in
  let map_id =
    List.fold_left2
      (fun acc (id1, srt1) (id2, srt2) ->
        if srt1 <> srt2 then
          begin
            let pr i s  = (string_of_ident i) ^":" ^ (string_of_sort s) in
              failwith ("uncompatible types: " ^ (pr id1 srt1) ^ " vs " ^ (pr id2 srt2))
          end;
        (*print_endline ((string_of_ident id1)^" -> "^(string_of_ident id2));*)
        IdMap.add id1 id2 acc)
      IdMap.empty
      def.parameters
      args
  in
  let def2 = subst_id map_id def in
  put_symbol def2;
  let rec var_to_const t = match t with
    | App (sym, args, sort) -> App (sym, List.map var_to_const args, sort)
    | Var (id, sort) ->
      if List.for_all (fun (i,_) -> i <> id) args then t
      else FormUtil.mk_free_const sort id
  in
  let var_to_cst = FormUtil.map_terms var_to_const in
  let output_map =
    List.fold_left
      (fun acc (id, _) -> IdMap.add id (make_output_fct def2 id) acc)
      IdMap.empty
      def2.outputs
  in
  let make_output (id, f) = (id, var_to_cst (FormUtil.subst output_map f)) in
  let renamed_struct = var_to_cst def2.structure in
  let renamed_outputs = List.map make_output def2.outputs in
    if Debug.is_debug () then
      begin
        print_endline ("renamed_struct: " ^ (Form.string_of_form renamed_struct));
        print_endline "renamed_outputs: ";
        List.iter
          (fun (id, r) ->
            print_endline ("  " ^ (string_of_ident id) ^ " ->\n" ^ (Form.string_of_form r)))
          renamed_outputs
      end;
    (renamed_struct, renamed_outputs)

(* add other predefined symbols*)
let _ =
  List.iter
    (fun (id, params, strct, out) ->
      Hashtbl.add
        symbols
        id
        { sym_name = id;
          parameters = params;
          structure = strct;
          outputs = out;
          pos_only = None
        }
    )
    Predefined.symbols
