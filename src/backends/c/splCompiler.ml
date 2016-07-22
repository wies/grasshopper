(** Translation of Abstract Syntax Tree to C program *)

open Util 
open Prog
open Sl
open Grass
open SplSyntax
open SplTypeChecker
open Format
open RemoveGhost
open Predef


(** Converts abstract syntax into a C program string and print it to output channel [oc].
 *  Assumes that [cu] has been type-checked and flattened. *)
let convert oc cu = 
  let idmap_to_list fs = (List.rev (IdMap.fold (fun k v a -> v :: a) fs [])) in
  (** Forward declarations for structs in order to allow mutual recursion. *)
  let pr_c_struct_fwd_decls ppf cu =
    let tds = cu.type_decls in
    let string_of_type_fwd_decl t_def t_id = 
      match t_def with
      | StructTypeDef _ -> "struct " ^ (string_of_ident t_id) ^ ";"
      | _ ->
          (* TODO: better error handling *)
          failwith "Cannot compile programs with undefined types"
    in
    fprintf ppf "%s"
      (String.concat 
        "\n" 
        (List.rev 
          (IdMap.fold 
            (fun k {t_name=t_id; t_def=t_def} a -> (string_of_type_fwd_decl t_def t_id) :: a) 
             tds 
            [])))
  in
  (** Translation of SPL struct declarations into C struct declarations. *)
  let pr_c_struct_decls ppf cu =
    let pr_c_field ppf v = 
      fprintf ppf "%s %s;" 
        (string_of_c_type v.v_type)
        (string_of_ident v.v_name)
    in
    let rec pr_c_fields ppf = function
      | []      -> ()
      | f :: [] -> pr_c_field ppf f
      | f :: fs -> fprintf ppf "%a@\n%a" pr_c_field f pr_c_fields fs         
    in
    let pr_c_struct ppf s =
      match s.t_def with
      | StructTypeDef fields ->
          fprintf ppf "typedef struct %s {@\n  @[%a@]@\n} %s;" 
            (string_of_ident s.t_name) 
            pr_c_fields (idmap_to_list fields)
            (string_of_ident s.t_name)
      | _ -> ()
    in
    let rec pr_c_structs ppf = function 
      | []      -> ()
      | s :: [] -> pr_c_struct ppf s
      | s :: ss -> fprintf ppf "%a@\n@\n%a" pr_c_struct s pr_c_structs ss
    in
    pr_c_structs ppf (idmap_to_list cu.type_decls)
  in
  (** Proc arguments, used in forward and regular procedure declaration -
   *  This slightly over-complex function that could probably be more 
   *  elegantly implemented puts together a list of strings that describe
   *  a procedure's arguments and the variables it returns (since, in the
   *  implementation, return variables are actually passed by reference into
   *  the function) and then this list is concatenated into a string using a
   *  comma and space as a delimiter. However, if the procedure has only one 
   *  return value, only the "true" arguments are printed, because the C
   *  return value is used in that case. *)
  let pr_c_proc_args ppf p =
    fprintf ppf "%s"
      (String.concat 
        ", " 
        (List.fold_right 
          (fun v a -> 
            ((string_of_c_type (IdMap.find v p.p_locals).v_type ) ^ 
            " " ^ 
            (string_of_ident v))
            :: a) 
          p.p_formals 
          (if ((List.length p.p_returns) <= 1) then
            []
          else
            (List.fold_right 
              (fun v a -> 
                ((string_of_c_type (IdMap.find v p.p_locals).v_type) ^ 
                "* " ^ (* Star operator used because return variables are passed in by reference *) 
                (string_of_ident v))
                :: a) 
              p.p_returns 
              []))))
  in
  (* Forward declarations for procs in order to allow mutual recursion. *)   
  let rec pr_c_proc_fwd_decls ppf cu =
    let pr_c_fwd_proc ppf p =
      fprintf ppf "%s %s (%a);" 
        (if ((List.length p.p_returns) != 1) then
          "void"
        else
          (string_of_c_type (IdMap.find (List.hd p.p_returns) p.p_locals).v_type))
        (string_of_ident p.p_name) 
        pr_c_proc_args p
    in
    let rec pr_c_fwd_procs ppf = function
      | []      -> ()
      | p :: [] -> pr_c_fwd_proc ppf p
      | p :: ps -> fprintf ppf "%a@\n%a" pr_c_fwd_proc p pr_c_fwd_procs ps
    in
    pr_c_fwd_procs ppf (idmap_to_list cu.proc_decls)
  in
  (** Translation of SPL proc declarations into C function declarations. *)
  let pr_c_proc_decls ppf cu =
    let rec pr_c_expr_args ppf = function
      | ([], _)      -> ()
      | (e :: [], cur_proc) -> fprintf ppf "%a" pr_c_expr (e, cur_proc) 
      | (e :: es, cur_proc) -> fprintf ppf "%a, %a" pr_c_expr (e, cur_proc) pr_c_expr_args (es, cur_proc)
    and pr_c_read ppf = function (from, index, cur_proc) ->
      (* The code below gets the type of the expression from and, if it is a
       * Map or an Array, prints some C code that reads the appropriate part of
       * the datastructure. *)
      (match from with 
        | (Ident (id, _)) as idExpr -> 
          (match (SplTypeChecker.type_of_expr cu cur_proc.p_locals idExpr) with 
            | MapType _ -> 
              fprintf ppf
                "(%a->%a)"
                pr_c_expr (index, cur_proc)
                pr_c_expr (idExpr, cur_proc)
            | ArrayType t1 ->
             (* The match statement in the following lines is required 
                 * because Arrays are stored as references while other values
                 * are not, so Arrays should be dereferenced one time less. *)
              if is_primitive t1 then 
                fprintf ppf "(%a->%s[%a])"
                  pr_c_expr (idExpr, cur_proc)
                  array_arr_field
                  pr_c_expr (index, cur_proc)
              else
                fprintf ppf
                  "((%s)(%a->%s[%a]))"
                  ((string_of_c_type t1) ^ "**")
                  pr_c_expr (idExpr, cur_proc)
                  array_arr_field
                  pr_c_expr (index, cur_proc)
            | _             -> fprintf ppf "/* ERROR: can't address such an object with Read. */")
        | _                 -> fprintf ppf "/* ERROR: can't address such an object with Read */")
    and pr_un_op ppf = function
      | (OpNot, e1)   -> fprintf ppf "(!%a)" pr_c_expr e1
      | (OpUMinus, e1) -> fprintf ppf "(-%a)" pr_c_expr e1
      | (OpBvNot, e1) -> fprintf ppf "(~%a)" pr_c_expr e1
      | (OpToInt, e1) -> fprintf ppf "((int) %a)" pr_c_expr e1
      | (OpToByte, e1) -> fprintf ppf "%a" pr_c_expr e1
      | (OpUPlus, e1) -> fprintf ppf "((char) %a)" pr_c_expr e1
      | ((OpLength | OpOld | OpKnown | OpArrayCells | OpArrayOfCell | OpIndexOfCell), _)  ->
          fprintf ppf "/* ERROR: no such unary operator. */"
    and pr_bin_op ppf = function
      | (e1, OpMinus, e2) -> fprintf ppf "(%a - %a)"  pr_c_expr e1 pr_c_expr e2
      | (e1, OpPlus,  e2) -> fprintf ppf "(%a + %a)"  pr_c_expr e1 pr_c_expr e2
      | (e1, OpMult,  e2) -> fprintf ppf "(%a * %a)"  pr_c_expr e1 pr_c_expr e2 
      | (e1, OpDiv, e2)   -> fprintf ppf "(%a / %a)"  pr_c_expr e1 pr_c_expr e2
      | (e1, OpMod, e2)   -> fprintf ppf "(%a %% %a)"  pr_c_expr e1 pr_c_expr e2
      | (e1, OpEq, e2)    -> fprintf ppf "(%a == %a)" pr_c_expr e1 pr_c_expr e2
      | (e1, OpGt, e2)    -> fprintf ppf "(%a > %a)"  pr_c_expr e1 pr_c_expr e2
      | (e1, OpLt, e2)    -> fprintf ppf "(%a < %a)"  pr_c_expr e1 pr_c_expr e2
      | (e1, OpGeq, e2)   -> fprintf ppf "(%a >= %a)" pr_c_expr e1 pr_c_expr e2 
      | (e1, OpLeq, e2)   -> fprintf ppf "(%a <= %a)" pr_c_expr e1 pr_c_expr e2
      | (e1, OpIn, e2)    -> fprintf ppf "(%a != %a)" pr_c_expr e1 pr_c_expr e2
      | (e1, OpAnd, e2)   -> fprintf ppf "(%a && %a)" pr_c_expr e1 pr_c_expr e2 
      | (e1, OpOr, e2)    -> fprintf ppf "(%a || %a)" pr_c_expr e1 pr_c_expr e2 
      | (e1, OpImpl, e2)  -> fprintf ppf "((!%a) || %a)" pr_c_expr e1 pr_c_expr e2 
      | (e1, OpBvAnd, e2) -> fprintf ppf "(%a & %a)" pr_c_expr e1 pr_c_expr e2 
      | (e1, OpBvOr, e2)  -> fprintf ppf "(%a | %a)" pr_c_expr e1 pr_c_expr e2 
      | (e1, OpBvShiftL, e2)  -> fprintf ppf "(%a << %a)" pr_c_expr e1 pr_c_expr e2 
      | (e1, OpBvShiftR, e2)  -> fprintf ppf "(%a >> %a)" pr_c_expr e1 pr_c_expr e2 
      | (_, (OpDiff | OpUn | OpInt), _) -> 
        fprintf ppf "/* ERROR: Sets not yet implemented */"
      | (_, (OpPts | OpSepStar | OpSepPlus | OpSepIncl), _) -> 
        fprintf ppf "/* ERROR: separation logic not yet implemented. */"
      (*| _ -> fprintf ppf "/* ERROR: no such Binary Operator */"*)
    and pr_c_expr ppf = function
      | (Null (_, _), _)           -> fprintf ppf "NULL"
      | (IntVal (i, _), _)         -> fprintf ppf "%s" (Int64.to_string i)
      | (BoolVal (b, _), _)        -> fprintf ppf (if b then "true" else "false")
      | (Read (from, index, _), cur_proc) -> pr_c_read ppf (from, index, cur_proc)
      | (ProcCall (id, es, _), cur_proc)  ->
        fprintf ppf "%s(%a)"
          (string_of_ident id)
          pr_c_expr_args (es, cur_proc)
      | (UnaryOp (OpLength, idexp, _), cur_proc) -> 
        fprintf ppf "(%a->%s)" 
          pr_c_expr (idexp, cur_proc)
          array_len_field
      | (UnaryOp  (op, e, _), cur_proc)          -> pr_un_op  ppf (op, (e, cur_proc))
      | (BinaryOp (e1, op1, e2, _, _), cur_proc) -> 
        pr_bin_op ppf ((e1, cur_proc), op1, (e2, cur_proc))
      | (Ident (id, _), {p_returns=p_returns})   ->
          if ((List.length p_returns) == 1) then
            fprintf ppf "%s" (string_of_ident id)
          else
            if (List.exists (fun lid -> lid == id) p_returns) then
              fprintf ppf "(*%s)" (string_of_ident id)
            else
              fprintf ppf "%s"    (string_of_ident id)
      | (New (t, args, _), _)             ->
        fprintf ppf "/* ERROR: New expression only allowed directly within an Assign or Free stmt. */"
      | ((Emp _|Setenum _|PredApp _|
        Binder _| Annot _), _) ->
        fprintf ppf "/* ERROR: expression type not yet implemented. */"
    in
    let rec pr_c_stmt ppf = 
      let rec pr_c_block ppf = function 
        | (Block ([], _), _)                 -> ()
        | (Block (s :: [], _), cur_proc)     -> fprintf ppf "%a" pr_c_stmt(s, cur_proc)
        | (Block (s :: ses, pos), cur_proc)  ->
          fprintf ppf "%a@\n%a" 
            pr_c_stmt  (s, cur_proc) 
            pr_c_block (Block(ses, pos), cur_proc)
        | _ -> fprintf ppf "/* ERROR: badly formed statement block. */"
      in
      let rec pr_c_assign_new ppf = function
        | (id, t, args, cur_proc) ->
          let usable_id_string =
            (if (List.exists (fun lid -> lid == id) cur_proc.p_returns) then 
              "(*" ^ (string_of_ident id) ^ ")"
            else  
               (string_of_ident id))
          in
          let type_stringc = (string_of_c_type_for_creation t) in
          let type_string = (string_of_c_type t) in
          (match (t, args) with 
            | (StructType _, [])  ->
              fprintf ppf "%s = ((%s) malloc(sizeof(%s)));" 
                usable_id_string
                type_string
                type_stringc
            | (ArrayType(t_sub), l :: []) ->
              fprintf ppf 
                "%s = %s( %a);"
                usable_id_string
                (array_new_proc_name t_sub)
                pr_c_expr (l, cur_proc)
            | _ -> fprintf ppf "/* ERROR: badly formed New expression. */"              
          )  
      in
      let rec pr_c_assign ppf = function
        | (Assign(Ident(id, _) :: [], New(t, args, _) :: [], _), cur_proc) ->
          pr_c_assign_new ppf (id, t, args, cur_proc)
        (* This branch is necessary because the next branch's pattern captures
         * all calls to procedures, but is only equipped to handle procedures
         * with multiple return values. *)
        | (Assign (v :: [], e :: [], _),cur_proc) -> 
          fprintf ppf "%a = %a;" 
            pr_c_expr (v, cur_proc)
            pr_c_expr (e, cur_proc)
        (* This branch passes in multiple return variables by reference
         * into the appropriate function in order to facilitate
         * multiple return variables within a C program. *)
        | (Assign (vs, ProcCall(id, es, _) :: [], _), cur_proc) ->
          let p = (IdMap.find id cu.proc_decls) in
          let rec pr_args_in ppf = function 
            | []      -> ()
            | e :: [] -> fprintf ppf "%a"     pr_c_expr (e, cur_proc)
            | e :: es -> fprintf ppf "%a, %a" pr_c_expr (e, cur_proc) pr_args_in es
          in
          let rec pr_args_out ppf = function 
            | []      -> ()
            | e :: [] -> fprintf ppf "&%a"    pr_c_expr (e, cur_proc)
            | e :: es -> fprintf ppf "%a, %a" pr_args_out [e] pr_args_out es
          in
          (** Printing arguments with various number of input and return variables *) 
          let pr_args_total ppf = function
            | (es, vs) ->
              if (((List.length es) == 0) && ((List.length vs) == 0)) then
                ()
              else if ((List.length es) == 0) then
                fprintf ppf "%a" pr_args_out vs
              else if ((List.length vs) == 0) then
                fprintf ppf "%a" pr_args_in  es
              else 
                fprintf ppf "%a, %a" pr_args_in es pr_args_out vs
          in
          fprintf ppf "%s(%a);"
            (string_of_ident p.p_name)
            pr_args_total (es, vs)
        | (Assign (v :: vs, e :: es, apos), cur_proc) -> 
          fprintf ppf "%a@\n%a"
            pr_c_stmt (Assign ([v], [e], apos), cur_proc)
            pr_c_stmt (Assign (vs,  es,  apos), cur_proc)
        | _ -> fprintf ppf "/* ERROR: badly formed Assign statement */"
      in
      let pr_c_dispose ppf = function (e, cur_proc) -> match e with
        | (Ident _ | New  _ | Read _ | ProcCall _) as e -> (match (SplTypeChecker.type_of_expr cu cur_proc.p_locals e) with
          | StructType _ | ArrayType _ ->
            fprintf ppf "free(%a);@\n"
              pr_c_expr (e, cur_proc) 
          | _ -> fprintf ppf "/* ERROR: a variable of such a type cannot be disposed. */" 
        )
        | BinaryOp _ -> fprintf ppf "/* ERROR: freeing the result of binary operation will possibly be implemented in the future for freeing Sets. */" 
        | (Null _ | Emp _ | Setenum _ | IntVal _ | BoolVal _ | PredApp _ | Binder _
        | UnaryOp _ | Annot _) ->
            fprintf ppf "/* ERROR: expression cannot be dispsosed */"
      in 
      (** Because SPL allows multiple return variables but C does not, yet in
       *  SPL only procedures with only one return value can be embedded in
       *  other expressions a number of cases are needed: no return value,
       *  single return value, double return values (as the base case of 
       *  multiple return values, since the single retun value case is something
       *  completely  different), more than 2 return values (as the inductive case),
       *  and the error case. *)
      let rec pr_c_return ppf = function
        | (Return([], _), {p_returns=[]}, []) ->
          fprintf ppf "return;"
        | (Return(e :: [], _), ({p_returns=r_single :: []} as cur_proc), r :: []) ->
          fprintf ppf "return %a;" 
            pr_c_expr (e, cur_proc)
        | (Return(e1 :: e2 :: [], _), cur_proc, r1 :: r2 :: []) ->
          fprintf ppf "*%s = %a;@\n*%s = %a;@\nreturn;"
            (string_of_ident r1)
            pr_c_expr (e1, cur_proc)
            (string_of_ident r2)
            pr_c_expr (e2, cur_proc)
        | (Return(e :: es, p), cur_proc, r :: rs) ->
          fprintf ppf "*%s = %a;@\n%a"
            (string_of_ident r)
            pr_c_expr (e, cur_proc)
            pr_c_return (Return(es,  p), cur_proc, rs)
        | _ -> fprintf ppf "/* ERROR: badly formed Return statement. */"
      in
      function 
      | (Skip (_), _) -> ()
      | (Block _, _) as b -> pr_c_block ppf b
      | (Assign _, _) as a -> pr_c_assign ppf a
      | (Dispose (e, _), cur_proc) -> pr_c_dispose ppf (e, cur_proc)
      | (If (cond, b1, b2, _), cur_proc) -> (match b2 with
        | Skip _ ->
         fprintf ppf "if (%a) {@\n  @[%a@]@\n}"
            pr_c_expr (cond, cur_proc)
            pr_c_stmt (b1,   cur_proc)
        | _      -> 
          fprintf ppf "if (%a) {@\n  @[%a@]@\n} else {@\n  @[%a@]@\n}"
            pr_c_expr (cond, cur_proc)
            pr_c_stmt (b1,   cur_proc)
            pr_c_stmt (b2,   cur_proc))
      | (Loop (_, pre, cond, body, _), cur_proc) -> 
        fprintf ppf "while (true) {@\n  @[%s%aif (!(%a)) {@\n  break;@\n}@\n%a@]@\n}"
          (match pre with 
            | Skip _ -> ""
            | _      -> "\n")
          pr_c_stmt (pre, cur_proc)
          pr_c_expr (cond, cur_proc)
          pr_c_stmt (body, cur_proc)
      | ((Return _) as r, cur_proc) -> pr_c_return ppf (r, cur_proc, cur_proc.p_returns)
      | (((Assume _)|(Assert _)|(Havoc _)), _) -> ()
      | (LocalVars _, _) -> fprintf ppf "/* ERROR: all LocalVars statements should have been removed by name resolution phase. */"
    in
    let pr_c_proc ppf p =
      (** Declarations of variables and their types are taken out of the AST,
       *  but we have to put them back in the C program, which is what the 
       *  function below does. *)
      let pr_c_decl_locals ppf p =
        (* We don't want to re-declare parameters or return variables (which
         * are either passed in as parameters or taken care of by the 
         * pre-processing function force_return. *)
        let do_not_decl_list = p.p_formals @ p.p_returns in
        let decl_list = 
          IdMap.fold 
            (fun k v acc -> 
              if (List.mem k do_not_decl_list) then
                acc
              else
                ((string_of_c_type v.v_type) ^ " " ^ 
                  (string_of_ident v.v_name) ^ ";" ) :: acc
            )
            p.p_locals 
            []
        in
        if ((List.length decl_list) == 0) then
          ()
        else
          fprintf ppf "%s@\n@\n" (String.concat "\n  " decl_list)
      in
      if ((List.length p.p_returns) == 1) then
        let default_return =
          Return(
            [Ident(
              (List.hd p.p_returns),
              pos_of_stmt(p.p_body))],
            pos_of_stmt(p.p_body))
        in
        (* Required because in SPL return statements at the end of functions are optional. *)
        let force_return = function
          | {p_body=Block([], pos1)} as proc1 ->
            {proc1 with p_body=Block(default_return :: [], pos1)}
          | {p_body=Block(ss, pos1)} as proc1 ->
            (match (List.hd (List.rev ss)) with
              | Return _ -> proc1
              | _        -> {proc1 with p_body=Block(ss@[default_return], pos1)})
          | {p_body=stmt1}           as proc1 ->
            {proc1 with p_body=Block(stmt1 :: [default_return], pos_of_stmt(stmt1))}
        in
        let pr_c_decl_return_var ppf p =
            let ret_var = (IdMap.find (List.hd p.p_returns) p.p_locals) in 
            fprintf ppf "%s %s;@\n"
            (string_of_c_type ret_var.v_type)
            (string_of_ident ret_var.v_name)
        in
        fprintf ppf "%s %s (%a) {@\n  @[%a%a%a@]@\n}"
          (string_of_c_type ((IdMap.find (List.hd p.p_returns) p.p_locals).v_type))
          (string_of_ident p.p_name) 
          pr_c_proc_args p
          pr_c_decl_return_var p
          pr_c_decl_locals p
          pr_c_stmt ((force_return p).p_body, p)
      else
        fprintf ppf "void %s (%a) {@\n  @[%a%a@]@\n}" 
          (string_of_ident p.p_name) 
          pr_c_proc_args p
          pr_c_decl_locals p
          pr_c_stmt (p.p_body, p)
    in
    let rec pr_c_procs ppf = function 
      | []      -> () 
      | p :: [] -> fprintf ppf "%a"         pr_c_proc p
      | p :: ps -> fprintf ppf "%a@\n@\n%a" pr_c_proc p pr_c_procs ps
    in
    pr_c_procs ppf (idmap_to_list cu.proc_decls)
  in
  (** Section functions -- functions that format particular categories of code
   *  (e.g. imports, structs, procs) completely so they can be integrated into
   *  the program total. *)
  let pr_c_import_section ppf () =
    fprintf ppf "%s@\n"
      "/*\n * Includes\n */";
    List.iter (fprintf ppf "%s@\n") includes
  in
  (** A section for structs and functions in C that form the base
   *  implementation of SPL. *) 
  let pr_c_preloaded_section ppf () =
    fprintf ppf "@\n%s@\n"
      "/*\n * Preloaded Code\n */";
    List.iter
      (fun t ->
        fprintf ppf "@\n%s@\n%s@\n"
          (array_decl t)
          (array_new_decl t) ) 
      [IntType; BoolType; ByteType; AnyRefType]
  in
  let pr_c_struct_section ppf cu =
    if (IdMap.is_empty cu.type_decls) then
      ()
    else
      fprintf ppf "@\n%s@\n%a@\n@\n%a"
        "/*\n * Structs\n */"
        pr_c_struct_fwd_decls cu
        pr_c_struct_decls     cu
  in 
  let pr_c_proc_section ppf cu =
    if (IdMap.is_empty cu.proc_decls) then
      ()
    else
      begin
        let cu_no_ghost = removeGhost cu in
        let has_body _ p = match p.p_body with
          | Skip _ -> false
          | _ -> true
        in
        (* remove the functions which does not have body *)
        let cu_no_skip = {cu_no_ghost with proc_decls = IdMap.filter has_body cu_no_ghost.proc_decls} in
          fprintf ppf "@\n@\n%s@\n%a@\n@\n%a"
            "/*\n * Procedures\n */"
            pr_c_proc_fwd_decls cu_no_ghost
            pr_c_proc_decls cu_no_skip
      end
  in
  (** This is just so it will compile for testing purposes. *)
  let pr_c_main_section ppf () =
    fprintf ppf "@\n@\n%s@\n%s@\n@\n"
    "/*\n * Main Function, here for compilability\n */"
    wrap_c_main
  in
  (** The actual work - feed-in the printing of the sections to the given out channel. *)
  let ppf = formatter_of_out_channel oc in
  fprintf ppf "%a%a%a%a%a"
    pr_c_import_section    () (* We pass unit (i.e. ()) simply to allow future *)
    pr_c_preloaded_section () (* changes to be easier to implement with printing functions. *)
    pr_c_struct_section    cu
    pr_c_proc_section      cu
    pr_c_main_section      ()

(** Convert compilation unit [cu] to a C program and print it to out channel [oc]. *)
let compile oc cu = convert oc cu
