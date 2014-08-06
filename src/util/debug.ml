open Logger

let lv = ref (int_of_level NOTICE)

let set_level lvl =
  lv := int_of_level lvl;
  if lvl = DEBUG
  then Printexc.record_backtrace true
  else Printexc.record_backtrace false

let show lvl = !lv >= (int_of_level lvl)

let is_debug () = show DEBUG
let is_info () = show INFO
let is_notice () = show NOTICE
let is_warn () = show WARN
let is_error () = show ERROR

let more_verbose () =
  let nlv = match (level_of_int !lv) with
    | DEBUG ->  DEBUG
    | INFO ->   DEBUG
    | NOTICE -> INFO
    | WARN ->   NOTICE
    | ERROR ->  WARN
    | FATAL ->  ERROR
    | NONE ->   FATAL
  in
    set_level nlv

let less_verbose () =
  let nlv = match (level_of_int !lv) with
    | DEBUG ->  INFO  
    | INFO ->   NOTICE
    | NOTICE -> WARN  
    | WARN ->   ERROR 
    | ERROR ->  FATAL 
    | FATAL ->  NONE
    | NONE ->   NONE
  in
  set_level nlv


(** always print this message *)
let amsg s =
  print_string s; flush_all ()

let debug  s = if show DEBUG  then amsg (s ())
let info   s = if show INFO   then amsg (s ())
let notice s = if show NOTICE then amsg (s ())
let warn   s = if show WARN   then amsg (s ())
let error  s = if show ERROR  then amsg (s ())

let phase s fn x =
  debug (fun () -> s () ^ "..."); 
  let res = fn x in
  debug (fun () -> "done.\n");
  res
