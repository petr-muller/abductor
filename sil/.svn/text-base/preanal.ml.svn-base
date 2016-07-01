(*
 *
 * Copyright (c) 2006-2008,
 *  Cristiano Calcagno    <ccris@doc.ic.ac.uk>
 *  Dino Distefano        <ddino@dcs.qmul.ac.uk>
 *  Peter O'Hearn         <ohearn@dcs.qmul.ac.uk>
 *  Hongseok Yang         <hyang@dcs.qmul.ac.uk>
 *  Oukseh Lee            <olee@dcs.qmul.ac.ul>
 * All rights reserved.
 *)

open Sil
open Cfg_new
module C = Cil
module G = Cfg_new
module E = Error.MyErr (struct let mode = Error.DEFAULT end)
open Format

module Vset = Set.Make (struct
  type t = pvar
  let compare = Pervasives.compare
end)

let get_call_site_node node =
  match node_get_preds node with
  | [h] -> h
  | _ -> assert false 

let is_not_function x =
  let st = Ident.name_to_string (Sil.pvar_get_name x) in
  try ignore (proc_name_to_proc_desc st); false with Not_found -> true

let rec use_exp (exp: exp) acc =
  match exp with
  | Var _ | Const_int _ | Const_fun _ | Sizeof _ -> acc
  | Lvar x -> if is_not_function x then Vset.add x acc else acc
  | Cast (_, e) | UnOp (_, e) | Lfield (e, _) -> use_exp e acc
  | BinOp (_, e1, e2) | Lindex (e1, e2) -> use_exp e1 (use_exp e2 acc)

and use_etl (etl: (exp * typ) list) acc =
  List.fold_left (fun acc (e, _) -> use_exp e acc) acc etl

and use_instr (instr: Sil.instr) acc =
  match instr with
  | Set (_, _, e, _) 
  | Letderef (_, e, _, _) -> use_exp e acc
  | Nullify _ -> assert false (** should not exist yet *)
  | Call (_, e, etl, _) -> use_etl etl acc

let def_instr (instr: Sil.instr) acc =
  match instr with
  | Set (e, _, _, _)
  | Call (Some (e, _, _), _, _, _) -> use_exp e acc
  | Call _ | Letderef _ -> acc
  | Nullify _ -> assert false (** should not exist yet *)

let def_instrl instrs acc = 
  List.fold_left (fun acc' i -> def_instr i acc') acc instrs

let def_node node acc = 
  match node_get_kind node with
  | Start_node _ | Exit_node _ | Join_node | Skip_node _ -> acc
  | Prune_node (il,_) -> 
      def_instrl il acc
  | Call_node _ -> acc 
  | Stmt_node il ->
      def_instrl il acc
  | Return_Site_node il ->
      match node_get_kind (get_call_site_node node) with
      | Call_node (_,pil,el) ->
          def_instrl pil (def_instrl il acc)
      | _ -> assert false

let compute_exp = use_exp
let compute_expl el s = List.fold_left (fun s e -> compute_exp e s) s el
let compute_instr instr s =
  use_instr instr (Vset.diff s (def_instr instr Vset.empty)) 
let compute_instrl = List.fold_right compute_instr

module Worklist = struct
  module S = Set.Make (struct
    type t = node
    let compare n1 n2 = node_compare n2 n1 
  end)

  let worklist = ref S.empty

  let reset _ = worklist := S.empty
  let add node = worklist := S.add node !worklist
  let add_list = List.iter add
  let pick _ =
    let min = S.min_elt !worklist in
    worklist := S.remove min !worklist;
    min
end

module Table: sig
  val reset: unit -> unit
  val get_post: node -> Vset.t
  val replace: node -> Vset.t -> unit
  val check_out: Vset.t -> node list -> unit
  val iter: Vset.t -> (node -> Vset.t -> Vset.t -> unit) -> unit
end = struct
  module H = Hashtbl.Make (struct
    type t = node
    let hash = Hashtbl.hash
    let equal = node_equal
  end)
  let table = H.create 1024 
  let reset _ = H.clear table
  let get_post node = try H.find table node with Not_found -> Vset.empty
  let get_pre init node = 
    match node_get_preds node with
    | [] -> init
    | h::t -> get_post h
  let replace node set = H.replace table node set

  let check_out' newset node =
    try
      let oldset = H.find table node in
      let newset' = Vset.union newset oldset in
      replace node newset';
      if not (Vset.equal oldset newset') then Worklist.add node
    with Not_found ->
      replace node newset; Worklist.add node

  let check_out set nl = List.iter (check_out' set) nl

  let iter init f = H.iter (fun node post -> f node (get_pre init node) post) table
end

(*
let nondet = Ident.string_to_name "nondet"

let ret_var_get_name (pdesc : proc_desc) : Sil.pvar =
  let ret_var = "retn_"^ proc_desc_to_proc_name pdesc in
  Sil.mk_pvar (Ident.string_to_name ret_var) (proc_desc_get_fundec pdesc)


let get_init pdesc =
  let fd = Cfg_new.proc_desc_get_fundec pdesc in
  let res1 = Vset.singleton (ret_var_get_name pdesc) in
  Vset.add (mk_pvar nondet fd) res1 
*)

(** Compute condidate nullable variables *)
let compute_candidates fd : Vset.t =
  let rec nullable_ty cil_ty =
    match cil_ty with
    | Cil.TVoid _ | Cil.TInt _ | Cil.TPtr _ | Cil.TEnum _ | Cil.TComp _ -> true
    | Cil.TNamed (ti, _) -> nullable_ty ti.Cil.ttype
    | _ -> false in
  let nullable_var cil_vi = nullable_ty cil_vi.Cil.vtype in
  let pvar vi = Sil.mk_pvar (Ident.string_to_name vi.Cil.vname) fd "" in
  let accumulate acc vil =
    List.fold_left 
      (fun s vi -> if nullable_var vi then Vset.add (pvar vi) s else s) 
      acc vil in
  accumulate (accumulate Vset.empty fd.Cil.sformals) fd.Cil.slocals

let analyze_proc pdesc cand =
  let exit_node = proc_desc_get_exit_node pdesc in
  Worklist.reset ();
  Table.reset ();
  Worklist.add exit_node;
  (* Table.replace exit_node (get_init pdesc); *)
  try
    while true do
      let curr = Worklist.pick () in
      let curr_d = Table.get_post curr in
      let preds = node_get_preds curr in
      let res =
	match node_get_kind curr with
	  | Start_node _ | Exit_node _ | Join_node | Skip_node _ -> curr_d
	  | Prune_node (il,e) -> 
	      compute_instrl il (compute_exp e curr_d)
	  | Call_node _ -> curr_d 
	  | Stmt_node il ->
              compute_instrl il curr_d
	  | Return_Site_node il ->
	      match node_get_kind (get_call_site_node curr) with
	      | Call_node (_,pil,etl) ->
		  let el = List.map fst etl
		  in compute_instrl pil (compute_expl el (compute_instrl il curr_d))
	      | _ -> assert false in
      Table.check_out (Vset.inter res cand) preds
    done
  with Not_found -> ()

let compile n dead_vars =
  List.map (fun pvar -> Nullify (pvar,node_get_loc n)) dead_vars

let rec annotate_node n dead_pvars =
  E.log "@[<6>    node %4d: " (node_to_sid n);
  E.log "%a@." Sil.pp_pvar_list dead_pvars;
  match node_get_kind n with
  | Stmt_node l -> 
      G.node_set_kind n (Stmt_node (l @ compile n dead_pvars)) 
  | Return_Site_node l ->
      G.node_set_kind n (Return_Site_node (l @ compile n dead_pvars)) 
  | Prune_node _ | Skip_node _ | Start_node _ -> 
      G.node_set_dead_pvar n dead_pvars
  | Call_node _ -> E.log "@[  AT CALL NODE@."; assert false
  | Join_node -> () (* E.log "@[  AT JOIN NODE@."; assert false *)
  | Exit_node _ -> E.log "@[  AT EXIT NODE@."; assert false


let analyze_and_annotate_proc pname pdesc =
  let fd = proc_desc_get_fundec pdesc in
  let cand = compute_candidates fd in
  if pname <> "main" || !Config.footprint_analysis then 
    begin
      analyze_proc pdesc cand;
      E.log "@[  PROCEDURE %s@." pname;
      Table.iter cand (fun n p q -> 
	let nonnull_pvars = Vset.inter (def_node n p) cand in
	let dead_pvars = Vset.elements (Vset.diff nonnull_pvars q) in
	if dead_pvars <> [] then annotate_node n dead_pvars);
      Table.reset ()
    end

let time = ref 0.0
let doit () =
  let init = Stats.get_current_time() in
  E.log "@[@\n#### Dead variable nullification ####@.";
  proc_desc_iter analyze_and_annotate_proc;
  time := !time +. (Stats.get_current_time() -. init)

let gettime () = !time
