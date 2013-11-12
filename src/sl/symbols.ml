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

let pred_struct (name, num) = (name ^ "_struct", num)
(*let pred_domain (name, num) = (name ^ "_domain", num)*)
let pred_naming (name, num) (p, _) = (name ^ "_" ^ p, num)

let make_output_fct sym id =
  let args =
    List.map
      (fun (i, s) -> FormUtil.mk_free_const ~srt:s i)
      (List.filter (fun (i, _) -> i <> id) sym.parameters)
  in
  let srt = snd (List.find (fun (i,_) -> i = id) sym.parameters) in
    FormUtil.mk_free_fun ~srt:srt (pred_naming sym.sym_name id) args

let pred_to_form p args =
  let def = get_symbol p in
  let map_id =
    List.fold_left2
      (fun acc (id1, srt1) (id2, srt2) ->
        assert (srt1 = srt2);
        IdMap.add id1 id2 acc)
      IdMap.empty
      def.parameters
      args
  in
  let map_const =
    List.fold_left2
      (fun acc (id1, srt1) (id2, srt2) ->
        IdMap.add id1 (FormUtil.mk_free_const ~srt:srt2 id2) acc)
      IdMap.empty
      def.parameters
      args
  in
  let map_output id =
    IdMap.add
      id
      (make_output_fct def id)
      map_const
  in
  let o id = FormUtil.subst (map_output id) in
    (FormUtil.subst map_const def.structure,
     List.map (fun (id, f) -> (IdMap.find id map_id, o id f)) def.outputs)

(* add othe predefined symbols*)
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
