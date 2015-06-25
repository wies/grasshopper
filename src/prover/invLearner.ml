(** {5 Module to learn invariants automatically} *)

open Util
open Grass
open GrassUtil
open Model

(** Find all pairs of ground terms in [terms] that point to the same
  location in a model [model]

  Returns a list of Grass.form, each asserting the equality of two such terms.
*)
let find_equalities model terms =
  (* Filter out only those terms that evaluate to locs *)
  let terms = TermSet.filter
		(function
		| Var (id, srt) -> is_loc_sort srt
		| App (sym, args, srt) -> is_loc_sort srt)
		terms
  in

  (* Compute a map from locations to all terms pointing to them *)
  let loc_to_term_map =
    let process_term term loc_to_term_map =
      let loc = eval model term in
      if ValueMap.mem loc loc_to_term_map then
	ValueMap.add loc (term :: (ValueMap.find loc loc_to_term_map)) loc_to_term_map
      else
	ValueMap.add loc [term] loc_to_term_map
    in
    TermSet.fold process_term terms ValueMap.empty
  in

  (* Then for each location, if it has more than one var, output all pairs *)
  let equalities_list =
    let print_terms_pointing_to_loc loc terms =
      Printf.printf "loc %s : " (string_of_value loc);
      List.iter (fun term -> Printf.printf "%s, " (string_of_term term)) terms;
      Printf.printf "\n";
    in

    let make_pairs_from_list list out_list =
      let make_pairs_with_elem (prefix_list, out_list) elem =
	(elem :: prefix_list),
	List.fold_left (fun out_list prev_elem ->
			(mk_eq prev_elem elem) :: out_list) out_list prefix_list
      in
      let _, out_list = List.fold_left make_pairs_with_elem ([], out_list) list in
      out_list
    in

    let process_loc loc term_list equalities_list =
       print_terms_pointing_to_loc loc term_list;
       make_pairs_from_list term_list equalities_list
    in

    ValueMap.fold process_loc loc_to_term_map []
  in
  Printf.printf "\nFound equalities:\n";
  List.iter (fun eq -> Printf.printf "%s\n" (string_of_form eq)) equalities_list;
  equalities_list

(** Tries to find more models given one model, by adding blocking clauses.
   @param session the current SmtLibSolver.session
   @param model the first model
   @param gts the ground terms in the VCs + preds
*)
let get_more_models session model gts =
  let equalities_list = find_equalities model gts in
  Printf.printf "\n\nDumping models to file:\nOriginal model in file %s\n"
		!Config.model_txt_file;

  let get_model_for_equality (model_num, session) eq =
    let session = SmtLibSolver.push session in
    Printf.printf "Trying to get a model for %s..." (string_of_form (mk_not eq));
    SmtLibSolver.assert_form session (mk_not eq);
    let result = Opt.get (SmtLibSolver.is_sat session) in
    if result then
      begin
	let file_name = (!Config.model_txt_file ^ (string_of_int model_num)) in
	Printf.printf "found. Model in %s\n" file_name;
	let model = Model.complete (Opt.get (SmtLibSolver.get_model session)) in
	let model_chan = open_out file_name in
	Model.output_txt model_chan model;
	close_out model_chan;

	(* Also output the dot file *)
	let model_chan = open_out (file_name ^ ".dot") in
	Model.output_graphviz model_chan model gts;
	close_out model_chan;

	(model_num+1, SmtLibSolver.pop session)
      end
    else
      begin
	Printf.printf "nope.\n";
	(model_num, SmtLibSolver.pop session)
      end
  in
  let _ = List.fold_left get_model_for_equality (1, session) equalities_list in
  (* Check sat again, otherwise next call to get_model fails *)
  let _ = SmtLibSolver.is_sat session in
  []


let assert_form_about_model session model gts =
  (* Printf.printf "\n\nGround terms are:\n"; *)
  (* TermSet.iter *)
  (*   (function *)
  (*     | App (FreeSym _, _, Set srt) as set_t -> *)
  (*        let set = eval model set_t in *)
  (*        let s = find_set_value model set srt in *)
  (*        let vals = List.map (fun e ->  string_of_sorted_value srt e) (ValueSet.elements s) in *)
  (*        let set_rep = String.concat ", " vals in *)
  (* 	 Printf.printf "%s = {%s}\n" (string_of_term set_t) set_rep; *)
  (* 	 print_endline (string_of_form ) *)
  (*     | t  -> Printf.printf "%s = %s\n" (string_of_term t) (string_of_value (eval model t))) gts; *)

  (* let session = SmtLibSolver.push session in *)
  (* SmtLibSolver.fix_model session; *)
  ()
