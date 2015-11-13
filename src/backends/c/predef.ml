(* A set of predefined elements *)

open Grass
open SplSyntax

let includes = ["#include <stdbool.h>";
                "#include <stdlib.h>";
                "#include <assert.h>"]

let is_primitive typ = match typ with
  | IntType | BoolType | ByteType | UnitType -> true
  | _ -> false

let array_prefix = "SPLArray_"
  
let array_struct_name typ = match typ with
  | IntType ->  array_prefix ^ "int"
  | BoolType -> array_prefix ^ "bool"
  | ByteType -> array_prefix ^ "char"
  | UnitType -> array_prefix ^ "void"
  | _ ->        array_prefix ^ "generic"

let rec string_of_c_type typ = match typ with
  | AnyRefType -> "void*" 
  | BoolType -> "bool"
  | IntType -> "int"
  | ByteType -> "char"
  | StructType id -> "struct " ^ (string_of_ident id) ^ "*"
  | ArrayType t -> (array_struct_name t) ^ "*"
  | MapType _| SetType _ -> "/* ERROR: Maps and Sets are not implemented yet. */"
  | _ -> "/* ERROR: no C equivalent (yet?). */"

let rec string_of_c_type_for_creation typ = match typ with
  | AnyRefType -> "void*" 
  | BoolType -> "bool"
  | IntType -> "int"
  | ByteType -> "char"
  | StructType id -> "struct " ^ (string_of_ident id)
  | ArrayType t -> array_struct_name t
  | MapType _| SetType _ -> "/* ERROR: Maps and Sets are not implemented yet. */"
  | _ -> "/* ERROR: no C equivalent (yet?). */"


let array_c_content_type typ = match typ with
  | IntType ->  "int"
  | BoolType -> "bool"
  | ByteType -> "char"
  | UnitType -> "void"
  | _ -> "void*"
let array_len_field  = "length"
let array_arr_field  = "arr"

let array_decl typ =
  "typedef struct {\n" ^ 
  "  int " ^ array_len_field ^ ";\n" ^ 
  "  " ^ (array_c_content_type typ) ^ " " ^ array_arr_field ^ "[];\n" ^
  "} " ^ (array_struct_name typ) ^ ";\n"

let array_free_proc_name typ = "freeSPLArray_" ^ (array_struct_name typ)

let array_free_decl typ = 
  "void " ^ (array_free_proc_name typ) ^"(" ^ (array_struct_name typ) ^ "* a) {\n" ^
  "  free(a->" ^ array_arr_field ^");\n" ^
  "  free(a);\n" ^
  "}"

let array_new_proc_name typ = "new" ^ (array_struct_name typ)

let array_new_decl typ = 
  let tpe = array_struct_name typ in
  let tpp = tpe ^ "*" in
  let cpp = array_c_content_type typ in
  tpp ^ " " ^ (array_new_proc_name typ) ^"(int size) {\n" ^
  "  "^tpp^" a = ("^tpp^")malloc(sizeof("^tpe^") + size * sizeof("^cpp^"));\n" ^
  "  assert(a != NULL);\n" ^
  "  a->"^array_len_field^" = size;\n" ^
  "  return a;\n" ^
  "}"

let wrap_c_main =
  "int main(int argc, char *argv[]) {\n" ^
  "  assert(argc <= 2);\n" ^
  "  int s = 0;\n" ^
  "  if (argc > 1) {\n" ^
  "    for(s = 0; argv[1][s] != 0; s++) { }\n" ^
  "    s++;\n"
  "  }\n" ^
  "  SPLArray_char* a = newSPLArray_char(s);\n" ^
  "  for(int i = 0; i < s; i++) {\n" ^
  "    a->arr[i] = argv[1][i];\n" ^
  "  }\n" ^
  "  return Main(a);\n" ^
  "}" 
