type level = NONE | FATAL | ERROR | WARN | NOTICE | INFO | DEBUG of int

let int_of_level = function
  | NONE -> 0 | FATAL -> 1 | ERROR -> 2 | WARN -> 3
  | NOTICE -> 4 | INFO -> 5 | DEBUG l -> 6 + l

let level_of_int = function
  | 0 -> NONE | 1 -> FATAL | 2 -> ERROR | 3 -> WARN
  | 4 -> NOTICE | 5 -> INFO | l when l > 5 -> DEBUG (l - 6)
  | i -> failwith ("invalid level: " ^ string_of_int i)

let lv = ref (int_of_level NOTICE)

let set_level lvl =
  lv := int_of_level lvl;
  match lvl with
  | DEBUG _ -> Printexc.record_backtrace true
  | _ -> Printexc.record_backtrace false

let show lvl = !lv >= (int_of_level lvl)

let is_debug l = show (DEBUG l)
let is_info () = show INFO
let is_notice () = show NOTICE
let is_warn () = show WARN
let is_error () = show ERROR

let more_verbose () =
  let nlv = match (level_of_int !lv) with
  | DEBUG l -> DEBUG (l + 1)
  | INFO -> DEBUG 0
  | NOTICE -> INFO
  | WARN -> NOTICE
  | ERROR -> WARN
  | FATAL -> ERROR
  | NONE -> FATAL
  in
  set_level nlv

let less_verbose () =
  let nlv = match (level_of_int !lv) with
  | DEBUG 0 -> INFO
  | DEBUG l -> DEBUG (l - 1)
  | INFO -> NOTICE
  | NOTICE -> WARN  
  | WARN -> ERROR 
  | ERROR -> FATAL 
  | FATAL -> NONE
  | NONE -> NONE
  in
  set_level nlv


(** always print this message *)
let amsg s =
  print_string s; flush_all ()

let debug  s = if show (DEBUG 0) then amsg (s ())
let debugl l s = if show (DEBUG l) then amsg (s ())
let info   s = if show INFO then amsg (s ())
let notice s = if show NOTICE then amsg (s ())
let warn   s = if show WARN then amsg (s ())
let error  s = if show ERROR then amsg (s ())

let phase s fn x =
  debug (fun () -> s () ^ "..."); 
  let res = fn x in
  debug (fun () -> "done.\n");
  res
