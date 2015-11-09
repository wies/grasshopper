(** SMT-LIB v2 abstract syntax *)
open Grass


type ident = Grass.ident

type pos = Grass.source_position

type sort = 
  | IntSort | BoolSort
  | BvSort of int
  | FreeSort of ident * sort list

type symbol =
  | BoolConst of bool
  | IntConst of int
  | BvConst of int * Int64.t
  | Ident of ident
  | Minus | Plus | Mult | Div
  | Eq | Gt | Lt | Geq | Leq
  | And | Or | Impl | Not | Ite
  (* bitvector theory *)
  | BvNot | BvAnd | BvOr | BvUlt
  | BvNeg | BvAdd | BvMul | BvUdiv | BvUrem
  | BvShl | BvShr | BvConcat | BvExtract of int * int

type binder = Exists | Forall

type term =
  | App of symbol * term list * pos option
  | Binder of binder * (ident * sort) list * term * pos option
  | Let of (ident * term) list * term * pos option
  | Annot of term * annotation * pos option

and annotation =
  | Name of ident
  | Pattern of term list
  | As of sort
        
type command =
  | SetInfo of string * string * pos option
  | SetOption of string * string * pos option
  | SetLogic of string * pos option
  | DeclareSort of ident * int * pos option
  | DefineSort of ident * ident list * sort * pos option
  | DeclareFun of ident * sort list * sort * pos option
  | DefineFun of ident * (ident * sort) list * sort * term * pos option
  | Assert of term * pos option
  | Push of int * pos option
  | Pop of int * pos option
  | CheckSat of pos option
  | GetModel of pos option
  | GetUnsatCore of pos option
  | Exit of pos option

type response =
  | Sat
  | Unsat
  | Unknown
  | Model of command list
  | UnsatCore of string list
  | Error of string

(** Constructor functions *)

let mk_const ?pos sym = App (sym, [], pos)

let mk_app ?pos sym ts = 
  match sym, ts with
  | Minus, [App (IntConst i, [], _)] -> 
      App (IntConst (-i), [], pos)
  | _, _ -> 
      App (sym, ts, pos)

let mk_binder ?pos b vs t =
  match vs with
  | [] -> t
  | _ -> Binder (b, vs, t, pos)

let mk_let ?pos defs t = Let (defs, t, pos)

let mk_annot ?pos t a = Annot (t, a, pos)

let mk_set_logic ?pos l = SetLogic (l, pos)
    
let mk_set_option ?pos o v = SetOption (o, v, pos)

let mk_set_info ?pos i v = SetInfo (i, v, pos)

let mk_declare_sort ?pos id arity = DeclareSort (id, arity, pos)

let mk_declare_fun ?pos id arg_srts res_srt = DeclareFun (id, arg_srts, res_srt, pos)

let mk_define_sort ?pos id args srt = DefineSort (id, args, srt, pos)

let mk_define_fun ?pos id args res_srt t = DefineFun (id, args, res_srt, t, pos)

let mk_assert ?pos t = Assert (t, pos)

let mk_push ?pos n = Push (n, pos)

let mk_pop ?pos n = Pop (n, pos)

let mk_check_sat ?pos () = CheckSat pos

let mk_get_model ?pos () = GetModel pos

let mk_get_unsat_core ?pos () = GetModel pos

let mk_exit ?pos () = Exit pos

(** Utility functions *)

let idents_in_term t =
  let rec iot acc = function
    | App (sym, ts, _) -> 
        let acc1 = match sym with
        | Ident id -> Grass.IdSet.add id acc
        | _ -> acc
        in
        List.fold_left iot acc1 ts
    | Binder (_, vs, t, _) ->
        let acc1 = List.fold_left (fun acc1 (id, _) -> Grass.IdSet.add id acc1) acc vs in
        iot acc1 t
    | Let (defs, t, _) ->
        let acc1 = List.fold_left (fun acc1 (id, t) -> iot (IdSet.add id acc1) t) acc defs in
        iot acc1 t
    | Annot (t, _, _) -> iot acc t
  in iot Grass.IdSet.empty t

(** Computes the set of identifiers of free variables occuring in term [t]
 ** union the accumulated set of identifiers [vars]. *)
let fv_in_term_acc vars t =
  let rec fvt bvs vars = function
  | App (sym, ts, _) -> 
      let vars1 = match sym with
      | Ident id when not (IdSet.mem id bvs) ->
          IdSet.add id vars
      | _ -> vars
      in
      List.fold_left (fvt bvs) vars1 ts
  | Annot (t, _, _) ->
      fvt bvs vars t
  | Binder (_, vs, t, _) ->
      let bvs1 =
        List.fold_left 
          (fun bvs1 (v, _) -> IdSet.add v bvs1)
          bvs vs 
      in
      fvt bvs1 vars t
  | Let (defs, t, _) ->
      let bvs1, vars1 = 
        List.fold_left (fun (bvs1, vars1) (v, t) ->
          IdSet.add v bvs1, fvt bvs vars1 t)
          (bvs, vars) defs
      in
      fvt bvs vars1 t
  in fvt IdSet.empty vars t

let fv_in_term t = fv_in_term_acc IdSet.empty t

(** Substitutes all free variables in term [t] according to substitution [sm].
 ** Capture avoiding. *)
let subst sm t =
  let rename_vars vs sm =
    let not_bound id _ = not (List.mem_assoc id vs) in
    let sm1 = IdMap.filter not_bound sm in 
    let occuring = IdMap.fold (fun _ t acc -> fv_in_term_acc acc t) sm IdSet.empty in
    let vs1, sm2 = 
      List.fold_right 
	(fun (x, srt) (vs1, sm2) ->
	  if Grass.IdSet.mem x occuring 
	  then 
	    let x1 = GrassUtil.fresh_ident (GrassUtil.name x) in
	    (x1, srt) :: vs1, IdMap.add x (App (Ident x1, [], None)) sm2
	  else (x, srt) :: vs1, sm2)
	vs ([], sm1)
    in vs1, sm2
  in
  let rec sub sm = function
    | App (Ident id, [], pos) as t ->
        (try IdMap.find id sm 
        with Not_found -> t)
    | App (sym, ts, pos) -> 
        App (sym, List.map (sub sm) ts, pos)
    | Binder (b, vs, t, pos) ->
        let vs1, sm1 = rename_vars vs sm in
        Binder (b, vs1, sub sm1 t, pos)
    | Let (defs, t, pos) ->
        let vs = List.map (fun (v, _) -> (v, IntSort)) defs in
        let vs1, sm1 = rename_vars vs sm in
        let defs1 = List.map2 (fun (v, _) (_, t) -> (v, sub sm t)) vs1 defs in
        Let (defs1, sub sm1 t, pos)
    | Annot (t, a, pos) -> 
        Annot (sub sm t, a, pos)
  in sub sm t

(** Expands all let expressions in term [t] *) 
let unletify t =
  let rec ul = function
  | App (sym, ts, pos) ->
      App (sym, List.map ul ts, pos)
  | Binder (b, vs, t, pos) ->
      Binder (b, vs, ul t, pos)
  | Let (defs, t, pos) ->
      let sm = 
        List.fold_left (fun sm (v, t) -> IdMap.add v (ul t) sm) IdMap.empty defs
      in
      ul (subst sm t)
  | Annot (t, a, pos) ->
      Annot (ul t, a, pos)
  in ul t

(** Pretty printing *)

open Format

let string_of_bv width value =
  let two = Int64.of_int 2 in
  let rec digits acc w v =
    assert(w >= 0);
    if w = 0 then
      begin
        if v <> Int64.zero then
          Debug.warn (fun () -> "string_of_bv: potential overflow with " ^ (Int64.to_string value));
        String.concat "" acc
      end
    else
      begin
        let d = if (Int64.rem v two) = Int64.one then "1" else "0" in
        digits (d :: acc) (w - 1) (Int64.shift_right v 1)
      end
  in
  "#b" ^ (digits [] width value)

let int_of_bits bits =
  let l = String.length bits in
  let rec fill acc i =
    if i > l then
      acc
    else
      begin 
        let lower =
          if bits.[i] = '0' then 0
          else if bits.[i] = '1' then 1
          else failwith ("bits are not 0 or 1: " ^ bits)
        in
        let acc2 = (acc lsl 1) + lower in
        fill acc2 (i+1)
      end
  in
  fill 0 0

let string_of_symbol = function
  | BoolConst b -> Printf.sprintf "%b" b
  | IntConst i -> string_of_int i
  | BvConst (w,i) -> string_of_bv w i
  | Ident id -> string_of_ident id
  | Plus -> "+"
  | Minus -> "-"
  | Mult -> "*"
  | Div -> "div"
  | Eq -> "="
  | Leq -> "<="
  | Geq -> ">="
  | Lt -> "<"
  | Gt -> ">"
  | And -> "and"
  | Or -> "or"
  | Impl -> "=>"
  | Not -> "not"
  | Ite -> "ite"
  | BvNot -> "bvnot"
  | BvAnd -> "bvand"
  | BvOr -> "bvor"
  | BvUlt -> "bvult"
  | BvNeg -> "bvneg"
  | BvAdd -> "bvadd"
  | BvMul -> "bvmul"
  | BvUdiv -> "bvudiv"
  | BvUrem -> "bvurem"
  | BvShl -> "bvshl"
  | BvShr -> "bvlshr"
  | BvConcat -> "concat"
  | BvExtract (i, j) -> "(_ extract " ^(string_of_int i)^ " " ^(string_of_int j)^")"

let pr_ident ppf id = fprintf ppf "%s" (string_of_ident id)

let rec pr_idents ppf = function
  | [] -> ()
  | [id] -> pr_ident ppf id
  | id :: ids -> fprintf ppf "%a@ %a" pr_ident id pr_idents ids

let rec pr_sort ppf = function
  | FreeSort (id, []) -> pr_ident ppf id
  | FreeSort (id, srts) -> fprintf ppf "@[<2>(%s@ %a)@]" (string_of_ident id) pr_sorts srts
  | BoolSort -> fprintf ppf "Bool"
  | IntSort -> fprintf ppf "Int"
  | BvSort size -> fprintf ppf "(_ BitVec %s)" (string_of_int size)

and pr_sorts ppf = function
  | [] -> ()
  | [srt] -> pr_sort ppf srt
  | srt :: srts -> fprintf ppf "%a@ %a" pr_sort srt pr_sorts srts

let pr_sym ppf sym = fprintf ppf "%s" (string_of_symbol sym)

let pr_binder ppf b =
  let b_str = match b with
  | Forall -> "forall"
  | Exists -> "exists"
  in 
  fprintf ppf "%s" b_str

let pr_var_decl ppf (x, srt) =
  fprintf ppf "@[<1>(%a@ %a)@]" pr_ident x pr_sort srt

let rec pr_var_decls ppf = function
  | [] -> ()
  | [v] -> fprintf ppf "%a" pr_var_decl v
  | v :: vs -> fprintf ppf "%a@ %a" pr_var_decl v pr_var_decls vs

let rec pr_term ppf = function
  | App (sym, [], _) -> pr_sym ppf sym
  | App (sym, ts, _) -> fprintf ppf "@[<2>(%a@ %a)@]" pr_sym sym pr_terms ts
  | Binder (b, vs, f, _) -> 
      fprintf ppf "@[<8>(%a@ @[<1>(%a)@]@ %a)@]" pr_binder b pr_var_decls vs pr_term f
  | Let (decls, t, _) ->
      fprintf ppf "@[<5>(let@ (%a) %a)@]" pr_let_decls decls pr_term t
  | Annot (t, a, _) -> pr_annot ppf (t, a)

and pr_terms ppf = function
  | [] -> ()
  | [t] -> pr_term ppf t
  | t :: ts -> fprintf ppf "%a@ %a" pr_term t pr_terms ts

and pr_let_decl ppf (id, t) =
  fprintf ppf "@[<2>(%a@ %a)@]" pr_ident id pr_term t

and pr_let_decls ppf = function
  | [] -> ()
  | [decl] -> pr_let_decl ppf decl
  | decl :: decls ->
      fprintf ppf "%a@ %a" pr_let_decl decl pr_let_decls decls
        
and pr_annot ppf (t, a) =
  match a with
  | Name id ->
      let id2 = Str.global_replace (Str.regexp " \\|(\\|)\\|<\\|>") "_" (string_of_ident id) in
      fprintf ppf "@[<3>(! %a@ @[:named@ %s@])@]" pr_term t id2
  | Pattern [] -> ()
  | Pattern ts ->
      fprintf ppf "@[<3>(! %a@ @[:pattern@ (%a)@])@]" pr_term t pr_terms ts
  | As srt ->
      fprintf ppf "@[<4>(as@ %a@ %a)@]" pr_term t pr_sort srt

let print_term out_ch t = fprintf (formatter_of_out_channel out_ch) "%a@?" pr_term t

let pr_command ppf = function
  | SetInfo (i, v, _) ->
      fprintf ppf "@[<10>(set-info@ %s@ %s)@]@\n" i v
  | SetOption (o, v, _) ->
      fprintf ppf "@[<12>(set-option@ %s@ %s)@]@\n" o v
  | SetLogic (l, _) ->
      fprintf ppf "@[<11>(set-logic@ %s)@]@\n" l
  | DeclareSort (id, n, _) ->
      fprintf ppf "@[<14>(declare-sort@ %a@ %d)@]@\n" pr_ident id n
  | DefineSort (id, svs, srt, _) ->
      fprintf ppf "@[<13>(define-sort@ %a@ (%a)@ %a)@]@\n" pr_ident id pr_idents svs pr_sort srt
  | DeclareFun (id, srts, srt, _) ->
      fprintf ppf "@[<13>(declare-fun@ %a@ (%a)@ %a)@]@\n" pr_ident id pr_sorts srts pr_sort srt
  | DefineFun (id, vs, srt, t, _) ->
      fprintf ppf "@[<12>(define-fun@ %a@ (%a)@ %a@ %a)@]@\n" pr_ident id pr_var_decls vs pr_sort srt pr_term t
  | Assert (t, _) ->
      fprintf ppf "@[<8>(assert@ %a)@]@\n" pr_term t
  | Push (n, _) -> fprintf ppf "@[<6>(push@ %d)@]@\n" n
  | Pop (n, _) -> fprintf ppf "@[<5>(pop@ %d)@]@\n" n
  | CheckSat _ -> fprintf ppf "(check-sat)@\n"
  | GetModel _ -> fprintf ppf "(get-model)@\n"
  | GetUnsatCore _ -> fprintf ppf "(get-unsat-core)@\n"
  | Exit _ -> fprintf ppf "(exit)@\n"

let rec pr_commands ppf = function
  | [] -> ()
  | cmd :: cmds ->
      fprintf ppf "%a%a" pr_command cmd pr_commands cmds

let print_command out_ch cmds = fprintf (formatter_of_out_channel out_ch) "%a@?" pr_command cmds
let print_commands out_ch cmds = fprintf (formatter_of_out_channel out_ch) "%a@?" pr_commands cmds
