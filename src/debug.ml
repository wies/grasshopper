let verbose = ref false

(** always print this message *)
let amsg s = print_string s; flush_all ()

(** print only if -v *)
let msg s = if !verbose then amsg s

let phase s fn x =
  msg (s ^ "..."); 
  let res = fn x in
  msg "done.\n";
  res
