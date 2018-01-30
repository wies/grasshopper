
open Util
open Grass
open GrassUtil
open Model

let string_of_sorted_value srt v =
  let rec elim_loc = function
    | Loc srt -> elim_loc srt
    | Set srt -> Set (elim_loc srt)
    | Array srt -> Array (elim_loc srt)
    | ArrayCell srt -> ArrayCell (elim_loc srt)
    | Map (dsrts, rsrt) -> Map (List.map elim_loc dsrts, elim_loc rsrt)
    | srt -> srt
  in
  match srt with
  | Int | Bool | Adt _ -> string_of_value v
  | _ ->
      let srt_str = string_of_sort (elim_loc srt) in
      srt_str ^ "!" ^ string_of_value v

let replace_lt_gt str =
  Str.global_replace (Str.regexp "<") "&lt;"
    (Str.global_replace (Str.regexp ">") "&gt;" str)

let replace_newlines str =
  Str.global_replace (Str.regexp "\n") "<br>" str

let output_json chan model =
  let string_of_sorted_value srt v = 
    "\"" ^ replace_lt_gt (string_of_sorted_value srt v) ^ "\""
  in
  let output_set s esrt =
    let vals = List.map (fun e ->  string_of_sorted_value esrt e) s in
    let set_rep = String.concat ", " vals in
    output_string chan ("[" ^ set_rep ^ "]")
  in
  let null_val srt = eval model (mk_null srt) in
  let output_value sym srt =
    match srt with
    | Loc _ | Bool | Int -> 
        let v = interp_symbol model sym ([], srt) [] in
        output_string chan (string_of_sorted_value srt v)
    | Set esrt ->
        (try
          let set = interp_symbol model sym ([], srt) [] in
          let s = find_set_value model set esrt in
          output_set (ValueSet.elements s) esrt
        with Undefined -> output_set [] esrt (* FIXME *))
    | Map ([dsrt], rsrt) ->
        let fld = interp_symbol model sym ([], srt) [] in
        let args = get_values_of_sort model dsrt in
        let arg_res = 
          Util.flat_map 
            (fun arg ->
              try
                let res = interp_symbol model Read ([srt; dsrt], rsrt) [fld; arg] in
                if is_loc_sort dsrt &&
                  (arg = null_val (struct_sort_of_sort dsrt) ||
                  res = null_val (struct_sort_of_sort dsrt))
                then [] 
                else  [(arg, res)]
              with Undefined -> [])
            args
        in
        output_string chan "[";
        Util.output_list chan 
          (fun (arg, res) -> 
            Printf.fprintf chan "{\"arg\": %s, \"res\": %s}" 
              (string_of_sorted_value dsrt arg) (string_of_sorted_value rsrt res)
          )
          ", " arg_res;
        output_string chan "]"
    | _ -> ()
  in
  let output_id ov id srt =
    Printf.fprintf chan "{\"name\": \"%s\", \"type\": \"%s\", \"value\": "
      id (string_of_sort srt);
    ov ();
    Printf.fprintf chan "}"
  in
  let output_symbol (sym, srt) = 
    output_string chan ", ";
    output_id (fun () -> output_value sym srt) (string_of_symbol sym) srt
  in
  let defs = 
    SortedSymbolMap.fold 
      (fun (sym, arity) _ defs ->
        match sym, arity with
        | (FreeSym _, ([], srt))
        | (Null, ([], srt)) -> (sym, srt) :: defs
        | _, _ -> defs) 
      model.intp []
  in
  output_string chan "[";
  SortSet.iter (fun srt ->
    let locs = get_values_of_sort model (Loc srt) in
    output_id (fun () -> output_set locs (Loc srt)) (string_of_sort (Loc srt)) (Set (Loc srt)))
    (get_loc_sorts model);
  List.iter output_symbol defs;
  output_string chan "]"
  
(* pretty printing *)
type shape = Box | Ellipse
type edge_style = Solid | Dashed

type graph_node = int * string * (string * string) list * shape (* id, name, data values, shape TODO more info for style *)

type graph_edge = int * int * string * edge_style * string (* src, dst, name, style, color TODO more info for style *)

type generic_graph_output = {
    header: out_channel -> unit;
    footer: out_channel -> unit;
    table: out_channel -> string -> (string * string) list -> unit;
    graph: out_channel -> graph_node list -> graph_edge list -> unit;
  }

let graphviz_output =
  let header chan = output_string chan "digraph Model {\ngraph[rankdir=LR];\n" in
  let footer chan = output_string chan "}\n" in
  let l = ref 0 in
  let out_tbl chan name assoc =
    let values = List.fold_left (fun acc (_,s) -> StringSet.add s acc) StringSet.empty assoc in
    if not (StringSet.is_empty values) then
      begin
        output_string chan ("{ rank = sink; Legend" ^ (string_of_int !l) ^ " [shape=none, margin=0, label=<\n");
        output_string chan "    <table border=\"0\" cellborder=\"1\" cellspacing=\"0\" cellpadding=\"4\">\n";
        output_string chan "      <tr>\n";
        output_string chan ("        <td colspan=\"2\"><b>" ^ (replace_lt_gt name) ^ "</b></td>\n");
        output_string chan "      </tr>\n";
        StringSet.iter
          (fun s ->
            let pairs = List.filter (fun (_,s2) -> s = s2) assoc in
            let keys = List.map fst pairs in
            let rowspan = List.length keys in
            Printf.fprintf chan "        <tr><td>%s</td><td rowspan=\"%s\">%s</td></tr>\n" (List.hd keys) (string_of_int rowspan) s;
            List.iter (fun k -> Printf.fprintf chan "        <tr><td>%s</td></tr>\n" k) (List.tl keys)
          ) values;
        output_string chan "</table>\n";
        output_string chan ">];\n";
        output_string chan "}\n";
      end
  in
  let out_graph chan nodes edges =
    let out_node (id,name,values,shape) =
      match shape with
      | Box ->
          Printf.fprintf chan "  \"%i\" [shape=none, margin=0, label=<\n" id;
          output_string chan "    <table border=\"0\" cellborder=\"1\" cellspacing=\"0\" cellpadding=\"4\">\n";
          Printf.fprintf chan "      <tr><td><b>%s</b></td></tr>\n" (replace_lt_gt name);
          List.iter
            (fun (f,v) -> Printf.fprintf chan "      <tr><td><b>%s = %s</b></td></tr>\n" (replace_lt_gt f) (replace_lt_gt v))
            values;
          output_string chan "</table>\n";
          output_string chan ">];\n"
      | Ellipse ->
        assert(values = []);
        Printf.fprintf chan "  \"%i\" [label=\"%s\"];" id name
    in
    let out_edge (src,dst,label,style,color) =
      match style with
      | Solid ->
        Printf.fprintf chan "\"%i\" -> \"%i\" [label=\"%s\", color=\"%s\"]\n" src dst (replace_lt_gt label) color
      | Dashed ->
        Printf.fprintf chan "\"%i\" -> \"%i\" [label=\"%s\", color=\"%s\", style=dashed]\n" src dst (replace_lt_gt label) color
    in
    List.iter out_node nodes;
    List.iter out_edge edges
  in
  { header = header;
    footer = footer;
    table = out_tbl;
    graph = out_graph }

let mixed_graphviz_html =
  let header chan =
    output_string chan "<!doctype html>
<html>
<head>
  <title>Model</title>
  <meta http-equiv=\"content-type\" content=\"text/html; charset=UTF-8\" />
  <style type=\"text/css\">
    .hspace { height: 2em }
    td,th {
       padding: 0 10px;
       border-bottom: 1px solid;
    }
    .selected { background: rgba(100,200,100,0.5) }
    .highlighted { background: rgba(200,100,100,0.5) }
    .indirect { background: rgba(100,100,200,0.5) }
   #heapgraph-container {
     height: 500px;
     width: 100%;
     border: 1px solid black;
   }
   svg {
     overflow: hidden;
     display: inline;
     width: inherit;
     height: inherit;
     min-width: inherit;
     min-height: inherit;
   }
  </style>
  <script src=\"http://ariutta.github.io/svg-pan-zoom/dist/svg-pan-zoom.min.js\"></script>
</head>
<body>

  <script type=\"text/javascript\">
    function forEachByTag(tag, callback) {
      var elements = document.getElementsByTagName(tag);
      for (var i = 0; i < elements.length; i++) {
        callback(elements[i]);
      }
    }
    function forEachByClass(cls, callback) {
      var elements = document.getElementsByClassName(cls);
      for (var i = 0; i < elements.length; i++) {
        callback(elements[i]);
      }
    }
    function iterateOverTableRows(fct) {
      forEachByTag('table', function(t) {
        for(var j = 1; j< t.rows.length; j++){
          fct(t.rows[j]);
        }
      });
    }
    function iterateOverTableCells(col, fct) {
      iterateOverTableRows(function(row){
        if (rows.cells.length > col) {
          fct(rows.cells[col]);
        }
      });
    }
    function iterateOverNodes(fct) {
      forEachByClass('node', fct);
    }
    function nodeLabel(node) {
      return node.getElementsByTagName('text')[0].innerHTML;
    }
    function contains(s1, s2) {
      return s1.indexOf(s2) > -1;
    }
    function fillNode(node) {
      var elements = node.getElementsByTagName('polygon');
      for (var i = 0; i < elements.length; i++) {
        elements[i].style.fill = \"rgba(100,250,100,0.7)\";
      }
      elements = node.getElementsByTagName('ellipse');
      for (var i = 0; i < elements.length; i++) {
        elements[i].style.fill = \"rgba(100,250,100,0.7)\";
      }
    }
    function resetNode(node) {
      var elements = node.getElementsByTagName('polygon');
      for (var i = 0; i < elements.length; i++) {
        elements[i].style.fill = \"none\";
      }
      elements = node.getElementsByTagName('ellipse');
      for (var i = 0; i < elements.length; i++) {
        elements[i].style.fill = \"none\";
      }
    }
    function resetHighlight() {
      //clean the current highlight
      var elements = document.getElementsByClassName('indirect');
      for (var i = 0; i < elements.length; i++) {
        elements[i].classList.remove('indirect');
      }
      elements = document.getElementsByClassName('selected');
      for (var i = 0; i < elements.length; i++) {
        elements[i].classList.remove('selected');
      }
      elements = document.getElementsByClassName('highlighted');
      for (var i = 0; i < elements.length; i++) {
        elements[i].classList.remove('highlighted');
      }
      iterateOverNodes(resetNode);
    }
    function highlightNodes(terms){
      iterateOverNodes(function(n) {
        if (contains(terms, nodeLabel(n))) {
          fillNode(n);
        }
      });
    }
    function traverseCells( content, clazz, clazzRm) {
      iterateOverTableRows(function(r) {
        for(var j = 0; j < r.cells.length; j++){
          var c = r.cells[j];
          if (contains(c.innerHTML, content)) {
            if (clazzRm !== undefined) {
              c.classList.remove(clazzRm);
            }
            c.classList.add(clazz);
          }
        }
      });
    }
    var lastSelected = undefined;
    function highlightRelated(cell, valueCell) {
      resetHighlight();
      resetHighlight();
      if (cell === lastSelected) {
        lastSelected = undefined;
      } else {
        lastSelected = cell;
        if (valueCell !== undefined) {
          highlightNodes(valueCell.innerHTML);
          traverseCells(valueCell.innerHTML, 'indirect', undefined);
        }
        highlightNodes(cell.innerHTML);
        traverseCells(cell.innerHTML, 'highlighted', 'indirect');
        cell.classList.remove('highlighted');
        cell.classList.add('selected');
      }
    }
    function highlightNode(node) {
      resetHighlight();
      resetHighlight();
      var l = nodeLabel(node);
      traverseCells(l, 'highlighted', undefined);
      fillNode(node);
    }
    function setTooltip(){
      forEachByTag('table', function(t) {
        var lbl;
        for(var j = 1; j < t.rows.length; j++){
          var row = t.rows[j].cells;
          if (row.length > 1) {
            lbl = row[1].innerHTML.replace(/&lt;/g,'<').replace(/&gt;/g,'>');
          }
          if (lbl !== undefined) {
            row[0].title = lbl;
          }
        }
      });
    }
    window.onload=function() {
      iterateOverTableRows(function(r) {
        if (r.cells.length > 0) {
          if (r.cells.length > 1) {
            r.cells[0].onclick=function(){
              highlightRelated(this, r.cells[1]);
            };
          } else {
            r.cells[0].onclick=function(){ highlightRelated(this, undefined); };
          }
        }
        if (r.cells.length > 1) {
          r.cells[1].onclick=function(){ highlightRelated(this, undefined); };
        }
      });
      iterateOverNodes(function(n) { n.onclick=function(){ highlightNode(this); } });
      var PanZoomGraph = svgPanZoom(\"#heapgraph\");
      setTooltip();
      document.body.ondragstart=function(){return false;};
      document.body.ondrop=function(){return false;};
    };

// Filter rows of the table
// Code from http://codepen.io/chriscoyier/pen/tIuBL
(function(document) {
    'use strict';

    var LightTableFilter = (function(Arr) {

        var _input;

        function _onInputEvent(e) {
            _input = e.target;
            var tables = document.getElementsByClassName(_input.getAttribute('data-table'));
            Arr.forEach.call(tables, function(table) {
                Arr.forEach.call(table.tBodies, function(tbody) {
                    Arr.forEach.call(tbody.rows, _filter);
                });
            });
        }

        function _filter(row) {
            var text = row.textContent.toLowerCase(), val = _input.value.toLowerCase();
            row.style.display = text.indexOf(val) === -1 ? 'none' : 'table-row';
        }

        return {
            init: function() {
                var inputs = document.getElementsByClassName('light-table-filter');
                Arr.forEach.call(inputs, function(input) {
                    input.oninput = _onInputEvent;
                });
            }
        };
    })(Array.prototype);

    document.addEventListener('readystatechange', function() {
        if (document.readyState === 'complete') {
            LightTableFilter.init();
        }
    });

})(document);

  </script>
  <div class=\"hspace\"></div>\n"
  in
  let footer chan =
    output_string chan "  <div class=\"hspace\"></div>
  <div>generated by <a href=\"https://github.com/wies/grasshopper\">GRASShopper</a></div>
</body>
</html>\n"
  in
  let out_tbl chan name assoc =
    let print_table_header title = 
      output_string chan "  <div class=\"hspace\"></div>\n";
      output_string chan "  <table class=\"values-table table\">\n";
      Printf.fprintf chan "    <tr><th colspan=\"2\"><b>%s</b></th></tr>\n" title;
    in
    let print_table_footer () =
      output_string chan "  </table>\n"
    in
    let values = List.fold_left (fun acc (_,s) -> StringSet.add s acc) StringSet.empty assoc in
      if not (StringSet.is_empty values) then
        begin
          print_table_header name;
          List.iter
            (fun (k, v) ->
              Printf.fprintf
              chan
              "    <tr><td>%s</td><td>%s</td></tr>\n"
              (* Alternatively, use <pre> block for k and v? *)
              (replace_lt_gt k) (replace_lt_gt v |> replace_newlines)
            )
            assoc;
          print_table_footer ()
        end
  in
  let out_graph chan nodes edges =
    let (out,inp) = Unix.open_process "dot -Tsvg" in
    graphviz_output.header inp;
    graphviz_output.graph inp nodes edges;
    graphviz_output.footer inp;
    flush inp;
    let rec read ok =
      let line = input_line out in
      let ok2 = ok || Str.string_match (Str.regexp "^<svg") line 0 in
      if ok2 then
        begin
	  let line = Str.replace_first (Str.regexp "^<svg") "<svg id=\"heapgraph\"" line in
          output_string chan line;
          output_string chan "\n"
        end;
      if line <> "</svg>" then read ok2
    in
    output_string chan "<div id=\"heapgraph-container\">\n";
    read false;
    output_string chan "</div>\n";
    (* Putting the filter box for the table here - below graph, above tables *)
    output_string chan "  <div class=\"hspace\"></div>\n";
    output_string chan "  <input type=\"search\" class=\"light-table-filter\" data-table=\"values-table\" placeholder=\"Filter\">\n";
    let _ = Unix.close_process (out, inp) in
    ()
  in
  { header = header;
    footer = footer;
    table = out_tbl;
    graph = out_graph }

let print_graph output chan model terms =
  let loc_sorts = get_loc_sorts model in
  let fld_srts = get_loc_fld_sorts model in
  let colors1 = ["blue"; "red"; "green"; "orange"; "darkviolet"] in
  let colors2 = ["blueviolet"; "crimson"; "olivedrab"; "orangered"; "purple"] in
  let all_flds =
    Util.flat_map
      (fun srt -> List.map (fun fld -> (srt, fld)) (get_values_of_sort model srt))
      (SortSet.elements fld_srts)
  in
  let fld_colors = Util.fold_left2 (fun acc fld color -> ((fld, color)::acc)) [] all_flds colors1 in
  let ep_colors = Util.fold_left2 (fun acc fld color -> (fld, color)::acc) [] all_flds colors2 in
  let get_color fsrt fld = try List.assoc (fsrt, fld) fld_colors with Not_found -> "black" in
  let out_tbl = output.table chan in
  (* Utils to pretty print sets and maps *)
  let rec pr_ext_val ppf ext_val =
    match ext_val with
    | BaseVal v -> Format.fprintf ppf "%s" (string_of_value v)
    | MapVal (m, d) -> Format.fprintf ppf "Map<TODO>"
    | SetVal s -> Format.fprintf ppf "Set<TODO>"
    | TermVal (vs, t) -> Format.fprintf ppf "Term<TODO>"
    | FormVal (vs, t) -> Format.fprintf ppf "Form<TODO>"
    | Undef -> Format.fprintf ppf "Undef"
  and pr_sorted_value ppf (term, srt) =
    try
      (match srt with
      | Set s ->
        let cnt = find_set_value model term s in
        Format.fprintf ppf "{@[<hv 2>%a@]}" pr_sorted_value_list
          (ValueSet.elements cnt |> List.map (fun v -> (v, s)));
      | Map (arg_s, res_s) ->
        let map_val, def_val = find_map_value model term arg_s res_s in
        Format.fprintf ppf "%a" (pr_map (arg_s, res_s)) (map_val, def_val)
      | _ ->
        Format.fprintf ppf "%s" (string_of_sorted_value srt term))
    with Undefined ->
        Format.fprintf ppf "%s" (string_of_sorted_value srt term)
  and pr_sorted_value_list ppf svals =
    pr_list_comma pr_sorted_value ppf svals
  and pr_map (arg_s, res_s) ppf (map, def_val) =
    let pr_map_elem ppf (args, v) = 
      Format.fprintf ppf "%a: %a" pr_sorted_value_list (List.combine args arg_s)
        pr_sorted_value (v, res_s)
    in
    Format.fprintf ppf "{@[<hv 2>%a@]}(__default: %a)" (pr_list_comma pr_map_elem)
      (ValueListMap.bindings map) pr_ext_val def_val
  in
  let str_of_t srt term = string_of_format pr_sorted_value (term, srt) in
  let output_constants () =
    let sorts =
      SortSet.filter
        (fun s -> match s with
        | Set _ | Loc _ | Map (Loc _ :: _, Loc _) -> false
        | _ -> true
        )
        (get_sorts model)
    in
    let rows =
      SortSet.fold
        (fun srt acc ->
          let syms = get_symbols_of_sort model ([], srt) in
          SymbolSet.fold
              (fun sym acc ->
                let str = string_of_symbol sym in
                let value = interp_symbol model sym ([], srt) [] in
                (str, (string_of_sorted_value srt value)) :: acc
              )
              syms acc
        )
        sorts []
    in
      out_tbl "constants" rows
  in
  let output_adts () =
    let str_adt (adt_defs, cons, cons_def, args) =
      let str_one_arg (v, (destr, srt)) =
        (* Convert FreeSyms in srt to Adts *)
        let rec convert = function
          | (Bool | Int | Byte | Pat) as s -> s
          | Loc e -> Loc (convert e)
          | Set e -> Set (convert e)
          | Array e -> Array (convert e)
          | ArrayCell e -> ArrayCell (convert e)
          | Adt (id, defs) -> Adt (id, defs)
          | Map (ds, r) -> Map (List.map convert ds, convert r)
          | FreeSrt id ->
            if List.mem_assoc id adt_defs then
              Adt (id, adt_defs)
            else FreeSrt id
        in
        Printf.sprintf "%s: %s" (string_of_ident destr) (string_of_format pr_sorted_value (v, convert srt))
      in
      Printf.sprintf "%s(%s)" (string_of_ident cons)
        (List.map str_one_arg (List.combine args cons_def) |> String.concat ", ")
    in
    (* TODO why doesn't this work? *)
    (* let pr_adt ppf (adt_defs, cons, cons_def, args) =
      let pr_one_arg ppf (v, (destr, srt)) =
        (* Convert FreeSyms in srt to Adts *)
        let rec convert = function
          | (Bool | Int | Byte | Pat) as s -> s
          | Loc e -> Loc (convert e)
          | Set e -> Set (convert e)
          | Array e -> Array (convert e)
          | ArrayCell e -> ArrayCell (convert e)
          | Adt (id, defs) -> Adt (id, defs)
          | Map (ds, r) -> Map (List.map convert ds, convert r)
          | FreeSrt id ->
            if List.mem_assoc id adt_defs then
              Adt (id, adt_defs)
            else FreeSrt id
        in
        Format.fprintf ppf "@[%a@]: @[%a@]" pr_ident destr pr_sorted_value (v, convert srt)
      in
      Format.fprintf ppf "@[%a(@[%a@])@]" pr_ident cons (pr_list_comma pr_one_arg)
        (List.combine args cons_def)
    in
    let string_of_adt adt_defs cons cons_def args =
      Util.string_of_format pr_adt (adt_defs, cons, cons_def, args)
    in *)
    let string_of_adt adt_defs cons cons_def args =
      str_adt (adt_defs, cons, cons_def, args)
    in
    let rows_of_srt acc srt =
      let row_of_sym adt_defs t_def sym =
        let str = string_of_symbol sym in
        let value = interp_symbol model sym ([], srt) [] in
        let value_str =
          (match value with
          | ADT (cons, args) ->
            let cons_def = List.assoc cons t_def in
            string_of_adt adt_defs cons cons_def args
          | _ ->
            failwith @@ "Expected ADT value but got " ^ (string_of_value value))
        in
        str, value_str
      in
      match srt with
      | Adt (t, adt_defs) -> 
        (* Find the defn of ADT t *)
        let t_def = List.assoc t adt_defs in
        let syms = get_symbols_of_sort model ([], srt) in
        SymbolSet.fold (fun sym acc -> (row_of_sym adt_defs t_def sym) :: acc) syms acc
      | _ -> []
    in
    let rows =
      SortSet.fold (fun srt acc -> rows_of_srt acc srt) (get_sorts model) []
    in
    out_tbl "ADTs" rows
  in
  let output_sets () =
    let print_sets srt =
      TermSet.fold
        (fun t acc -> match t with
          | App (FreeSym _, _, Set srt1) as set_t when srt = srt1 ->
              (try
                let set = eval model set_t in
                let set_rep = str_of_t (Set srt1) set in
                ((string_of_term set_t), set_rep) :: acc
              with Failure _ | Undefined -> acc)
          | _ -> acc)
        terms []
    in
    let all_loc_sets = SortSet.fold (fun srt acc -> (print_sets (Loc srt)) @ acc) loc_sorts [] in
    let int_sets = print_sets Int in
    out_tbl "sets" (int_sets @ all_loc_sets)
  in
  (* functions and pred *)
  let output_freesyms () =
    let (_, funs) = TermSet.fold
      (fun t (seen, acc) -> match t with
        | App ((FreeSym _ as sym), args, srt) when args <> [] ->
            (try
              let str_of a = str_of_t (sort_of a) (eval model a) in
              let args_str = List.map str_of args in
              let lhs = (string_of_symbol sym) ^ "(" ^ (String.concat ", " args_str) ^ ")" in
                if StringSet.mem lhs seen then
                  (seen, acc)
                else
                  begin
                    let res = eval model t in
                    let rhs = str_of_t srt res in
                     (StringSet.add lhs seen, (lhs, rhs) :: acc)
                  end
            with _ -> (seen,acc))
        | _ ->
            (seen,acc)
      ) terms (StringSet.empty, []) 
    in
    out_tbl "predicates and functions" funs
  in
  let node_counter = ref 0 in
  let sorted_value_to_node = Hashtbl.create 64 in
  let sym_to_node = Hashtbl.create 64 in
  let nodes = ref [] in
  let declare_value srt v values =
    try Hashtbl.find sorted_value_to_node (srt, v)
    with Not_found ->
      begin
        (*print_endline ("declare_value: " ^ (string_of_sorted_value srt v));*)
        let i = !node_counter in
        node_counter := i + 1;
        nodes := (i, string_of_sorted_value srt v, values,Box) :: !nodes;
        Hashtbl.add sorted_value_to_node (srt, v) i;
        i
      end
  in
  let declare_symbol sym =
    try Hashtbl.find sym_to_node sym
    with Not_found ->
      begin
        let i = !node_counter in
        node_counter := i + 1;
        nodes := (i, string_of_symbol sym, [], Ellipse) :: !nodes;
        i
      end
  in
  let get_node srt v =
    try Hashtbl.find sorted_value_to_node (srt, v)
    with Not_found ->
      failwith ("not found: " ^ (string_of_sorted_value srt v))
  in
  let edges = ref [] in
  let declare_locs srt =
    let locs = get_values_of_sort model (Loc srt) in
    let output_data_fields loc rsrt =
      SymbolSet.fold
        (fun fld acc ->
          try 
            let f = interp_symbol model fld ([], field_sort srt rsrt) [] in
            let fld_str = string_of_symbol fld in
            let m, d = find_map_value model f [Loc srt] rsrt in
            let v = fun_app model (MapVal (m, d)) [loc] in
            (fld_str, (string_of_sorted_value rsrt v)) :: acc
          with Undefined -> acc)
        (get_symbols_of_sort model ([], field_sort srt rsrt)) []
    in
    let data_fields_sort =
      SortSet.fold
        (fun k acc -> match k with
        | FreeSrt _ -> k :: acc
        | _ -> acc
        )
        (get_sorts model) [Int;Bool]
    in
    List.iter
      (fun loc ->
        let values = List.flatten (List.map (output_data_fields loc) data_fields_sort) in

        let _ = declare_value srt loc values in ())
      locs
  in
  let mk_graph srt =
    let flds = get_values_of_sort model (loc_field_sort srt) in
    let locs = get_values_of_sort model (Loc srt) in
    let read_arity = [loc_field_sort srt; Loc srt], Loc srt in
    let find_term = find_term model in
    let rsrts =
      SortSet.fold
        (function
          | Map ([Loc srt1], Loc rsrt) when srt1 = srt -> SortSet.add rsrt
          | _ -> fun rsrts -> rsrts)
        fld_srts SortSet.empty
    in
    let output_loc_vars () = 
      SymbolSet.iter (fun sym ->
        let v = interp_symbol model sym ([], Loc srt) [] in
        let src = declare_symbol sym in
        let dst = Hashtbl.find sorted_value_to_node (srt, v) in
        edges := (src, dst, "", Solid, "black") :: !edges)
        (get_symbols_of_sort model ([], Loc srt))
    in
    let output_flds rsrt =
      let filter_null r =
        (not !Config.model_null_edge) &&
        (interp_symbol model Null ([], Loc rsrt) [] = r)
      in
      let fld_srt = Map ([Loc srt], Loc rsrt) in
      let flds = get_values_of_sort model fld_srt in
      let read_arity = [fld_srt; Loc srt], Loc rsrt in
      List.iter 
        (fun f ->
          List.iter (fun l ->
            try
              let r = interp_symbol model Read read_arity [f; l] in
              if not (filter_null r) then 
                try 
	          let label = string_of_term (find_term f fld_srt) in
                  let src = get_node srt l in
                  let dst = get_node rsrt r in
                  edges := (src,dst,label,Solid,get_color fld_srt f) :: !edges
                with _ -> ()
            with Undefined -> ())
            locs)
        flds
    in
    let output_cell_array () =
      match srt with
      | Array esrt ->
          let cell_srt = Loc (ArrayCell esrt) in
          let cell_locs = get_values_of_sort model cell_srt in
          List.iter (fun l ->
            try
              List.iter (fun c ->
                let l1 = interp_symbol model ArrayOfCell ([cell_srt], Loc (Array esrt)) [c] in
                if l1 = l then begin
                  let src = declare_value (ArrayCell esrt) c [] in
                  let dst = get_node srt l in
                  edges := (src, dst, "array", Solid, "black") :: !edges;
                  let cells = interp_symbol model ArrayCells ([Loc (Array esrt)], Map ([Int], cell_srt)) [l] in
                  let i = interp_symbol model IndexOfCell ([cell_srt], Int) [c] in
                  let c1 = interp_symbol model Read ([Map ([Int], cell_srt); Int], cell_srt) [cells; i] in
                  if c1 = c then
                    edges := (dst, src, Int64.to_string (int_of_value i), Solid, "black") :: !edges
                end)
                cell_locs
            with Not_found | Undefined -> ())
            locs
      | _ -> ()
    in
    let output_simple_array () =
      match srt with
      | Array (Loc inner as esrt) ->
        let _ = TermSet.fold
          (fun t seen -> match t with
            | App (Read, [array_state; arr ; idx], s) when s = esrt && sort_of arr = (Loc srt) ->
              (try
                let i = eval model idx in
                if (Int64.compare (int_of_value i) Int64.zero) >= 0 then
                  begin
                    let _src = eval model arr in
                    let src = get_node srt _src in
                    let _dst = eval model t in
                    let dst = get_node inner _dst in
                    let astate = eval model array_state in
                    let label = (string_of_value astate) ^ ", " ^ (string_of_value i) in
                    let id = (string_of_sorted_value srt _src) ^ (string_of_sorted_value inner _dst) ^ label in
                    if not (StringSet.mem id seen) then
                      begin
                        let color = try List.nth colors2 (Int64.to_int (int_of_value astate))
                                    with Failure _ | Undefined -> "black" in
                        edges := (src, dst, label, Solid, color) :: !edges;
                        StringSet.add id seen
                      end
                    else
                      seen
                  end
                else
                  seen
              with Failure _ | Undefined -> seen)
            | _ -> seen)
          terms StringSet.empty
        in
          ()
      | _ -> ()
    in
    let output_array () =
      if !Config.simple_arrays
      then output_simple_array ()
      else output_cell_array ()
    in
    let output_reach () =
      List.iter 
        (fun f ->
          List.iter
            (fun l ->
              let r = succ model srt f l in
              if is_defined model Read read_arity [f; l] || r == l then () else
              let src = get_node srt l in
              let dst = get_node srt r in
	      let label = string_of_term (find_term f (loc_field_sort srt)) in
              edges := (src,dst,label,Dashed,get_color (loc_field_sort srt) f) :: !edges)
            locs)
        flds
    in
    let output_eps () =
      let arg_srts = [loc_field_sort srt; Set (Loc srt); Loc srt] in
      let m, _ = get_interp model EntPnt (arg_srts, Loc srt) in
      ValueListMap.iter (function 
        | [f; s; l] -> fun v ->
            let fld = find_term f (loc_field_sort srt) in
            let set = find_term s (Set (Loc srt)) in
            let src = get_node srt l in
            let dst = get_node srt v in
            let color = try List.assoc (srt, f) ep_colors with Not_found -> "black" in
            let label = "ep(" ^ (string_of_term fld) ^ ", " ^ (string_of_term set) ^ ")" in
              edges := (src,dst,label,Dashed,color) :: !edges
        | _ -> fun v -> ()) 
        m
    in
      SortSet.iter output_flds rsrts;
      output_array ();
      output_loc_vars ();
      output_reach ();
      output_eps ()
  in
  SortSet.iter declare_locs loc_sorts;
  SortSet.iter mk_graph loc_sorts;
  output.header chan;
  output.graph chan !nodes !edges;
  (* TODO array of non-loc stuff *)
  output_constants ();
  output_adts ();
  output_sets ();
  output_freesyms ();
  output.footer chan
 
let output_html = print_graph mixed_graphviz_html
let output_graph = print_graph graphviz_output
