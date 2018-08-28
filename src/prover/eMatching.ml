(** E-Matching.

  Implements a variant of the e-matching technique presented in this paper:
      Efficient E-Matching for SMT Solvers
      Leonardo de Moura and Nikolaj Bjorner, CADE 2007

*)

open Util
open Grass
open GrassUtil

module CC = CongruenceClosure

(** E-matching code trees *)
type ematch_code =
  | Init of sorted_symbol * int * ematch_code
  | Bind of int * sorted_symbol * int * ematch_code
  | Check of int * term * ematch_code
  | Compare of int * int * ematch_code
  | Choose of ematch_code list
  | Yield of int IdMap.t * form
  | ChooseApp of int * ematch_code * CC.Node.t list list

let continuation = function
  | Init (_, _, c) -> c
  | Bind (_, _, _, c) -> c
  | Check (_, _, c) -> c
  | Compare (_, _, c) -> c
  | _ -> failwith "illegal argument to continuation"

let max_reg c =
  let rec mr m = function
    | Init (_, i, c) 
    | Check (i, _, c)
    | ChooseApp (i, c, _) -> mr (max m i) c
    | Bind (i, _, o, c)
    | Compare (i, o, c) -> mr (max (max m i) o) c
    | Choose cs ->
        List.fold_left mr m cs
    | Yield _ -> m
  in
  mr 0 c

let mk_choose c1 c2 =
  match c1, c2 with
  | Choose cs1, Choose cs2 -> Choose (cs1 @ cs2)
  | Choose cs1, _ -> Choose (cs1 @ [c2])
  | _, Choose cs2 -> Choose (c1 :: cs2)
  | _ -> Choose [c1; c2]

(** Work queue for pattern compilation *)
module WQ = PrioQueue.Make
    (struct
      type t = int
      let compare = compare
    end)
    (struct
      type t = term
      let compare t1 t2 =
        if is_ground_term t1 && not @@ is_ground_term t2 then -1
        else match t1, t2 with
        | Var _, App _ -> -1
        | App _, Var _ -> 1
        | _ -> compare t1 t2  
    end)

(** Compile the list of patterns [patterns] into an ematching code tree *)
let compile patterns =
  let add_args_to_queue w o args =
    List.fold_left
      (fun (w', o') arg -> WQ.insert o' arg w', o' + 1)
      (w, o) args
  in
  let rec compile f pattern w v o =
    let rec c w v o =
      if WQ.is_empty w then init f pattern v o else
      let i, t, w' = WQ.extract_min w in
      match t with
      | Var (x, _) when not @@ IdMap.mem x v ->
          c w' (IdMap.add x i v) o
      | Var (x, _) ->
          Compare (i, IdMap.find x v, c w' v o)
      | t when is_ground_term t ->
          Check (i, t, c w' v o)
      | App (sym, args, _) ->
          let w'', o' = add_args_to_queue w' o args in
          Bind (i, sorted_symbol_of t |> Opt.get, o, c w'' v o')
    in
    c w v o
  and init f pattern v o =
    match pattern with
    | App (_, args, _) as t :: pattern ->
        let w, o' = add_args_to_queue WQ.empty o args in
        Init (sorted_symbol_of t |> Opt.get, o, compile f pattern w v o')
    | Var _ :: _ -> failwith "TODO"
    | [] -> Yield (v, f)
  in
  let seq cs fchild =
    let rec s = function
      | Init (sym, o, c) :: cs -> Init (sym, o, s cs)
      | Check (i, t, c) :: cs -> Check (i, t, s cs)
      | Compare (i, j, c) :: cs -> Compare (i, j, s cs)
      | Bind (i, sym, o, c) :: cs -> Bind (i, sym, o, s cs)
      | [] -> fchild
      | _ -> assert false
    in
    s (List.rev cs)
  in
  let branch f pattern comps fchild w o =
    seq comps (mk_choose (compile f pattern w IdMap.empty o) fchild)
  in
  let compatible pattern w = function
    | Init (sym, o, _) ->
        if WQ.is_empty w then 
          match pattern with
          | App (_, args, _) as t :: pattern'
            when sorted_symbol_of t = Some sym ->
              let w', _ = add_args_to_queue WQ.empty o args in
              Some w'
          | _ -> None
        else None
    | Check (i, t, _) ->
        (match WQ.find_opt i w with
        | Some t' when t = t' -> Some (WQ.delete i w)
        | _ -> None)
    | Compare (i, j, _) ->
        let ti_opt = WQ.find_opt i w in
        let tj_opt = WQ.find_opt j w in
        (match ti_opt, tj_opt with
        | Some (Var _ as ti), Some tj when ti = tj ->
            Some (WQ.delete j w)
        | _ -> None)
    | Bind (i, sym, o, _) ->
        (match WQ.find_opt i w with
        | Some (App (_, args, _) as t) when sorted_symbol_of t = Some sym ->
            let w', _ = add_args_to_queue w o args in
            Some (WQ.delete i w')
        | _ -> None)
    | _ -> None
  in
  let rec insert_code f pattern w o comps incomps code =
    match code with
    | Choose cs ->
        if incomps = [] then
          let code', score = insert_choose f pattern cs w o in
          seq comps code', score + List.length comps
        else branch f pattern comps (seq incomps code) w o, List.length comps
    | Yield _ ->
        branch f pattern comps (seq incomps code) w o, List.length comps
    | code ->
        let code' = continuation code in
        compatible pattern w code |>
        Opt.map (fun w' -> insert_code f pattern w' o (code :: comps) incomps code') |>
        Opt.lazy_get_or_else (fun () -> insert_code f pattern w o comps (code :: incomps) code')
  and insert_choose f pattern cs w o =
    let cs', _, best =
      List.fold_right
        (fun code (cs', cs, best) ->
          match insert_code f pattern w o [] [] code with
          | code', score when score > best ->
              code' :: cs, code :: cs, score
          | _ -> code :: cs', code :: cs, best
        )
        cs ([], [], 0) 
    in
    if best = 0
    then Choose (compile f pattern w IdMap.empty o :: cs), 0
    else Choose cs', best
  in   
  List.fold_left
    (fun code (f, pattern) ->
      let code', _ = insert_code f pattern WQ.empty (max_reg code) [] [] code in
      code'
    )
    (Choose []) patterns

(** Run the given e-matching code tree. Yields a list of instantiated formulas. *)
let run code ccgraph =
  let rec run insts (regs: CC.Node.t array) = function
    | Init (sym, o, next) :: stack ->
        let apps = CC.get_apps ccgraph sym in
        run insts regs (ChooseApp (o, next, apps) :: stack)
    | Bind (i, sym, o, next) :: stack ->
        let apps = CC.get_apps_of_node ccgraph (regs.(i)) sym in
        run insts regs (ChooseApp (o, next, apps) :: stack)
    | Check (i, t, next) :: stack ->
        if CC.node_of_term ccgraph t = regs.(i)
        then run insts regs (next :: stack)
        else run insts regs stack
    | Compare (i, j, next) :: stack ->
        if regs.(i) = regs.(j)
        then run insts regs (next :: stack)
        else run insts regs stack
    | Choose cs :: stack ->
        run insts regs (cs @ stack)
    | Yield (vs, f) :: stack ->
        let sm = IdMap.map (fun i -> CC.term_of_node ccgraph regs.(i)) vs in
        run (subst sm f :: insts) regs stack
    | ChooseApp (o, next, args :: apps) :: stack ->
        let _ =
          List.fold_left
            (fun i arg -> regs.(i) <- arg; i + 1)
            o args
        in
        run insts regs (next :: ChooseApp (o, next, apps) :: stack)
    | ChooseApp (_, _, []) :: stack ->
        run insts regs stack
    | [] -> insts
  in
  run [] (Array.make (max_reg code) (CC.node_of_term ccgraph mk_true_term)
