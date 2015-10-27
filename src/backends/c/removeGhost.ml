open Util 
open Prog
open Sl
open Grass
open SplSyntax
open Debug


let removeGhost cu =

  (* collect the ghosts *)
  let keep_ghost map =
    let vars = IdMap.filter (fun _ v -> v.v_ghost) map in
    IdMap.fold (fun _ v acc -> IdSet.add v.v_name acc) vars IdSet.empty
  in
  let gs_global = keep_ghost cu.var_decls in
  let gs_procs = IdMap.map (fun p -> keep_ghost p.p_locals) cu.proc_decls in

  (* utils *)
  let is_ghost_arg name idx =
    let proc = IdMap.find name cu.proc_decls in
    let v = List.nth proc.p_formals idx in
    let gs = IdMap.find name gs_procs in
    IdSet.mem v gs
  in
  let is_ghost_return name idx =
    let proc = IdMap.find name cu.proc_decls in
    let v = List.nth proc.p_returns idx in
    let gs = IdMap.find name gs_procs in
    IdSet.mem v gs
  in
  let is_ghost name id =
    let gproc = IdMap.find name gs_procs in
    IdSet.mem id gproc || IdSet.mem id gs_global
  in

  (* do the work *)
  warn (fun () -> "ToDo strip the ghost\n");
  cu
