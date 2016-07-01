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

open Cil
open Pretty
open Cfg_new
open Prop
open Format

module E = Error.MyErr (struct let mode = Error.DEFAULT end)

let debug = false

let sym_exec_type = 0

let guard_error = ref 0

(* ddino's implementation of RHS algoritm as described in POPL 95 paper.
 * Hongseok cleaned and optimized the implementation.
 *
 * Notation:
 * sp is the unique _starting_ node of procedure p
 * ep is the unique _exit_ node of procedure p
 * callp is the set of calling nodes of procedure p
 * retp is the set of return nodes of procedure p
 * returnSite(n) maps the call node n to the corresponding return site node
 *)    


(* =============== START of Print Functions =============== *)

(* print dotty file the list of proposition  of a node *)
let dotty_node node d error_state=
  let rec list_prop2propset d p =
    match d with 
      [] -> p
    |h::ls -> list_prop2propset ls (Propset.propset_add  h p) 
  in
  let pset=Propset.propset_empty in
  let name_file=if error_state then 
    "error_node"^(string_of_int (node_to_sid node ))^".dot" 
  else
    "result_node"^(string_of_int (node_to_sid node ))^".dot" in 
  let pset=list_prop2propset d pset in
  Propset.pp_propset_dotty_file name_file pset 


(* print final results of the analysis *)
let print_results dset =
  E.err "@[<2>  %a@\n@." Propset.pp_propset dset;
  Propset.pp_propset_dotty_file "result.dot" dset 


(* =============== END of Print Functions =============== *)




(* =============== Basic types ========================== *)

type control_flow = 
    | NoBranching of Propset.propset
    | Branching of Propset.propset  * Propset.propset

type control_flow_tagged = control_flow * (Cil.exp option)


(* defintions related to edge_set *)

type start_info = int
let start_compare = Ident.int_compare

module EdgeSet = 
  Set.Make(struct
    type t = start_info * Prop.prop
    let compare (p, s) (q, t) = 
      match start_compare p q with
      | 0 -> Prop.prop_compare s t
      | i -> i
  end)

type edge_set = EdgeSet.t


(* =============== END of basic types =============== *)

let ident_pair_compare (id1,id1') (id2,id2') =
  let n = Ident.ident_compare id1 id2
  in if n <> 0 then n
    else Ident.ident_compare id1' id2'


module Imap = Map.Make
  (struct
    type t = start_info
    let compare = start_compare
  end)

module Pmap = Map.Make
  (struct
    type t = Prop.prop
    let compare = Prop.prop_compare
  end)

module Shash = Hashtbl.Make 
  (struct
    type t = int * start_info
    let equal (i, p) (j, q) = i=j && p=q
    let hash = Hashtbl.hash
  end)

module IntSet =
  Set.Make(struct
    type t = int
    let compare = Ident.int_compare
  end)

module Join_table = struct
  let table : Propset.propset Shash.t = Shash.create 1024
  let reset () = Shash.clear table
  let find i p = 
    try Shash.find table (i, p) with Not_found -> Propset.propset_empty
  let put i p dset = Shash.replace table (i, p) dset
  let remove_nodes (nodes : node list) : unit =
    let idset =
      List.fold_right IntSet.add (List.map node_to_sid nodes) IntSet.empty in
    let to_delete = ref [] in
    let mark_to_delete (i,s) ps =
      if IntSet.mem i idset
      then to_delete := (i,s) :: !to_delete
    in
      Shash.iter mark_to_delete table;
      List.iter (Shash.remove table) !to_delete
end

let partition_edgeset es =
  let pm_insert k e m =
    let s = try Imap.find k m with Not_found -> Propset.propset_empty in
    Imap.add k (Propset.propset_add e s) m in
  EdgeSet.fold (fun (s, p) -> pm_insert s p) es Imap.empty

(* =============== START of the path_edge object =============== *)    

type path_edge = edge_set Inthash.t 
    (* indexed by the sid of the current node, not the start node *)

let path_edge_visited : path_edge = Inthash.create 1024

let path_edge_todo : path_edge = Inthash.create 1024

let path_edge_reset _ = 
  Inthash.clear path_edge_visited;
  Inthash.clear path_edge_todo;
  Join_table.reset()

let htable_retrieve (htable : path_edge) (key : int) : edge_set =
  try 
    Inthash.find htable key
  with Not_found ->
    Inthash.replace htable key EdgeSet.empty;
    EdgeSet.empty

(*
let path_edge_elements (filter : edge_sharp -> bool) : edge_sharp list =
  let f key edge_set res = 
    let edge_set' = EdgeSet.filter filter edge_set in
    let edge_list = EdgeSet.elements edge_set' 
    in edge_list :: res in
  let edge_list_list = Inthash.fold f path_edge_visited [] 
  in List.flatten edge_list_list
*)

let path_edge_get_visited (sid:int) =
  let visited = htable_retrieve path_edge_visited sid 
  in EdgeSet.elements visited

let path_edge_visiting_check (node: node) : bool =
  match node_get_kind node with
  | Skip_node l when (!Config.join_level <= 1) && (l = "loop") -> true
  | Stmt_node _ | Prune_node _ | Skip_node _ -> false
  | _ -> true

let path_edge_put_todo (node: node) (d:edge_set) : bool =
  let sid = node_to_sid node in
  let old_todo = htable_retrieve path_edge_todo sid in
  match path_edge_visiting_check node with
  | false ->
      Inthash.replace path_edge_todo sid (EdgeSet.union d old_todo);
      true
  | _ ->
      let old_visited = htable_retrieve path_edge_visited sid in
      let d' = EdgeSet.diff d old_visited in 
      let todo_new = EdgeSet.union old_todo d' in
      Inthash.replace path_edge_todo sid todo_new;
      not (EdgeSet.is_empty todo_new)

let path_edge_checkout_todo (node: node) : edge_set = 
  try
    let sid = node_to_sid node in
    let todo = Inthash.find path_edge_todo sid in
    Inthash.replace path_edge_todo sid EdgeSet.empty;
    begin
      if path_edge_visiting_check node then
	let visited = Inthash.find path_edge_visited sid in
	let new_visited = EdgeSet.union visited todo in  
	Inthash.replace path_edge_visited sid new_visited
    end;
    todo  
  with Not_found -> 
    assert false

let path_edge_is_empty_todo (sid:int) : bool = 
  try 
    let todo = Inthash.find path_edge_todo sid 
    in EdgeSet.is_empty todo
  with Not_found ->
    false


(* =============== END of the edge_set object =============== *)





(* =============== START of the proc_summary object =============== *)    

(* indexed by the name of the procedure *)

module Proc = struct

  module Obs = struct
    type t = start_info * Cfg_new.node * Prop.prop 
      (* (source, call node, frame) *)

    let compare obs1 obs2 = 
      let (src1,nd1,frame_d1) = obs1 in
      let (src2,nd2,frame_d2) = obs2 in
      let n = start_compare src1 src2  in
      if n <> 0 then n 
      else 
	let n = Cfg_new.node_compare nd1 nd2 in 
	if n <> 0 then n 
	else 
          Prop.prop_compare frame_d1 frame_d2 
  end

  module ObsSet = Set.Make(Obs)

  type proc_tbl = Propset.propset Inthash.t
  type obs_tbl = (ObsSet.t option) Inthash.t  (* None if summary is completed *)
  type eqs_tbl = ((Ident.ident * Ident.ident) list) Inthash.t

  type proc_summary = { 
    mutable ps_idtbl: int Pmap.t; (* maps prop to unique id for this proc *)
    mutable ps_idsize: int;
    ps_tbl: proc_tbl; 
    ps_obs: obs_tbl;
    ps_eqs: eqs_tbl (* equations introduced for cutpoints. *)
  }
  type proc_summaries = (string, proc_summary) Hashtbl.t

  let table: proc_summaries = Hashtbl.create 128

  let summary_create () =
    { ps_idtbl = Pmap.empty;
      ps_idsize = 0;
      ps_tbl = Inthash.create 64;
      ps_obs = Inthash.create 64;
      ps_eqs = Inthash.create 64 }

  let summary_find (proc_name: string) : proc_summary =
    try
      Hashtbl.find table proc_name
    with Not_found -> 
      let new_entry = summary_create () in 
      Hashtbl.add table proc_name new_entry; 
      new_entry 

  let get_id (ps: proc_summary) (in_d: Prop.prop) =
    try 
      Pmap.find in_d ps.ps_idtbl 
    with Not_found ->
      let id = ps.ps_idsize in
      ps.ps_idtbl <- Pmap.add in_d id ps.ps_idtbl;
      ps.ps_idsize <- ps.ps_idsize + 1;
      id

  let rec ident_pair_list_compare id_pairs1 id_pairs2 =
    match id_pairs1, id_pairs2 with
      | [],[] -> 0
      | [], _ -> -1
      | _, [] -> 1
      | id_pair1::l1, id_pair2::l2 ->
	  let n = ident_pair_compare id_pair1 id_pair2 in
	    if n <> 0 then n
	    else ident_pair_list_compare l1 l2

  let find (ps: proc_summary) id : Propset.propset = 
    try Inthash.find ps.ps_tbl id with Not_found -> Propset.propset_empty
  let add (ps: proc_summary) id dset = 
    Inthash.replace ps.ps_tbl id (Propset.propset_union dset (find ps id))
  let replace (ps: proc_summary) id dset = 
    Inthash.replace ps.ps_tbl id dset

  let find_eqs (ps : proc_summary) id : (Ident.ident * Ident.ident) list =
    try Inthash.find ps.ps_eqs id with Not_found -> [] 
  let find_obs (ps: proc_summary) id : ObsSet.t =
    try (match Inthash.find ps.ps_obs id with Some obs -> obs | None -> ObsSet.empty)
    with Not_found -> ObsSet.empty
  let id_is_complete (ps: proc_summary) id : bool = 
    try (match Inthash.find ps.ps_obs id with Some obs -> false | None -> true)
    with Not_found -> false

  let add_obs (ps: proc_summary) id eqs obs =
    if id_is_complete ps id then () (* don't add if summary is complete *)
    else
      let old_eqs = find_eqs ps id
      in     
	Inthash.replace ps.ps_obs id (Some (ObsSet.add obs (find_obs ps id)));
	if old_eqs = [] then
	  Inthash.replace ps.ps_eqs id eqs
	    (* Hongseok : sanity check below
	       else if ident_pair_list_compare old_eqs eqs <> 0 then 
	       assert false 
	    *)
	else ()

  let gc_observers (proc_name: string) =
    let ps = summary_find proc_name in
    let obslist = Inthash.tolist ps.ps_obs in
    let mark_as_completed (id,_) = Inthash.replace ps.ps_obs id None
    in List.iter mark_as_completed obslist
 
  let gc_tables (proc_name: string) = 
    let nodes = proc_desc_get_nodes (proc_name_to_proc_desc proc_name) in
    let gc_path_edges () = 
      let ids = List.map (fun node -> node_to_sid node) nodes in
      let remove_from_table table = List.iter (Inthash.remove table) ids in
      remove_from_table path_edge_todo; 
      remove_from_table path_edge_visited 
    in
    Join_table.remove_nodes nodes;
    if !Config.gc_summaries >= 3 then gc_path_edges()

  let notify (ps: proc_summary) id (todo: Obs.t -> unit) =
    ObsSet.iter todo (find_obs ps id)

  let display () =
    let ent_count = ref 0 in
    let obs_count = ref 0 in
    let res_count = ref 0 in
      E.err "@[@\n#### Procedure summary tables ####@\n@.";
      Hashtbl.iter (fun name summary ->
        ent_count := summary.ps_idsize;
        obs_count := 0;
        res_count := 0;
        Pmap.iter (fun prop id ->
  	  let res = find summary id in
  	  let res_size = Propset.propset_size res in
  	  let obs = find_obs summary id in
	  let obs_size = ObsSet.cardinal obs in 
             res_count := res_size + !res_count;
             obs_count := obs_size + !obs_count) summary.ps_idtbl;
        E.err "@[<2>++++ %s ++++@\n" name;
        E.err "Entries:%d@\n" !ent_count;
        E.err "Observers:%d@\n" !obs_count;
        E.err "Results:%d@\n" !res_count;
        (*
        Pmap.iter (fun prop id ->
  	  let res = find summary id in
  	  let res_size = Propset.propset_size res in
  	  let obs = find_obs summary id in
	  let obs_size = ObsSet.cardinal obs in 
             E.err "@\n# of obs: %d, # of res:%d@\n" obs_size res_size;
             E.err "ENTRY:@\n%a@\n" Prop.pp_prop prop;
             ObsSet.iter (fun (_,_,prop_obs) ->
	       E.err "@\nOBS:@\n%a@\n" pp_prop prop_obs) obs;
	     E.err "@\nRES:@\n%a@\n" Propset.pp_propset res) summary.ps_idtbl;
        *)
        E.err "@.") table

  let display_stats () =
    let tot_ent_count = ref 0 in
    let tot_obs_count = ref 0 in
    let tot_res_count = ref 0 in 
      Hashtbl.iter (fun name summary ->
        tot_ent_count := summary.ps_idsize + !tot_ent_count;
        Pmap.iter (fun prop id ->
  	  let res = find summary id in
  	  let res_size = Propset.propset_size res in
  	  let obs = find_obs summary id in
	  let obs_size = ObsSet.cardinal obs in 
             tot_obs_count := obs_size + !tot_obs_count;
             tot_res_count := res_size + !tot_res_count) summary.ps_idtbl) table;
      E.err "@[<2>#### Statistics for Procedure Summaries ####@\n";
      E.err "Total Entries:%d@\n" !tot_ent_count;
      E.err "Observers:%d@\n" !tot_obs_count;
      E.err "Results:%d@\n@." !tot_res_count
      
end

(* =============== END of the proc_summary object =============== *)




(* =============== START of the work_list object =============== *)    
  
module WorkList =
  Set.Make(struct
    type t = node
    let compare = node_compare 
  end)

let garbage_collect_summary node =
  let proc_desc = node_get_proc_desc node in
  let proc_name = proc_desc_to_proc_name proc_desc
  in
    if !Config.gc_summaries >= 1 then Proc.gc_observers proc_name;
    if !Config.gc_summaries >= 2 then Proc.gc_tables proc_name

let worklist : WorkList.t ref = ref WorkList.empty

let work_list_is_empty _ : bool =
  WorkList.is_empty !worklist

let work_list_add (node : node) : unit = 
  worklist := WorkList.add node !worklist

let work_list_remove _ : node =
  try 
    let min = WorkList.min_elt !worklist 
    in
      worklist := WorkList.remove min !worklist;
      min
  with Not_found -> begin
    E.err "@....Work list is empty! Impossible to remove edge...@."; 
    assert false
  end

let work_list_elements (filter : node -> bool) : node list =
  List.filter filter (WorkList.elements !worklist)

(* =============== END of the work_list object =============== *)



(* ===== Start of symbolic execution without abstraction ===== *)

(* Get the name of the return variable of procedure pdesc. *)
let ret_var_get_name (pdesc : proc_desc) : Sil.pvar =
  let ret_var = "retn_"^proc_desc_to_proc_name pdesc in
  Sil.mk_pvar (Ident.string_to_name ret_var) (proc_desc_get_fundec pdesc) ""


(* Get the type of the return variable of procedure pdesc. *)
let ret_var_get_type (pdesc : proc_desc) : Sil.typ = 
  let cil_ret_type = proc_desc_get_cil_ret_type pdesc 
  in Trans.trans_typ cil_ret_type


(* Deallocates pointsto predicates for local variables, formals and
 * the return variable of proc_desc. *)
let deallocate_locals_formals_ret (pdesc : proc_desc) (d : Prop.prop) = 
  let get_name_of_cilvar x = Sil.mk_pvar (Ident.string_to_name x.vname) (proc_desc_get_fundec pdesc) "" in
  let locals = proc_desc_get_locals pdesc in
  let formals = proc_desc_get_formals pdesc in
  let names_of_locals_formals = List.map get_name_of_cilvar (locals @ formals) in 
  let name_of_ret_var = ret_var_get_name pdesc in
  let names_of_ret_var_locals_formals = name_of_ret_var :: names_of_locals_formals in
  let _=
    E.log "@[<2>.... Deallocate local variables, parameters and return variable from d1 ....@\nd1=%a@\n@."  Prop.pp_prop d in
  let d5 = Prop.prop_dispose_stack_proc d names_of_ret_var_locals_formals
  in 
    E.log "@[<2>.... Resulting state after deallocation ....@\nd5=%a@\n@."  Prop.pp_prop d5;
    d5

(* =========== End of sym. exec. without abstraction ========= *)





(* =============== START of symbolic execution =============== *)

(* First, does the symbolic execution for the instructions "instrs".
 * Then, existentially quantifies all the identifiers in ids. Finally,
 * applies the abstraction. *)
let doInstr2 (dset: Propset.propset) (ids, instrs): Propset.propset = 
  let _ = 
    E.log "@[.... Translated Instrs ....@\n%a@." Sil.pp_instr_list instrs in
  let post_dset = List.fold_left SymExec.lifted_sym_exec dset instrs in
  let quantified_dset = SymExec.lifted_exist_quantify (Sil.fav_from_list ids) post_dset in    
  let new_dset = Abs.lifted_abstract quantified_dset 
  in 
    E.log "@[<2>.... After Symbolic Execution ....@\n%a@\n@." Propset.pp_propset new_dset; 
    new_dset 

let converging_node node =
  match node_get_succs node with
  | [] -> assert false
  | [h] -> List.length (node_get_preds h) > 1
  | _ -> false

let exe_instrs dset instrl = 
  E.log "@[.... Translated Instrs ....@\n%a@." Sil.pp_instr_list instrl;
  let dset' = List.fold_left SymExec.lifted_sym_exec dset instrl in
  E.log "@[<2>.... After Symbolic Execution ....@\n%a@\n@." Propset.pp_propset dset'; 
  dset'

let remove_temp_pvars dset node =
  exe_instrs dset (Preanal.compile node (node_get_dead_pvar node))

let remove_temp_vars dset node =
  SymExec.lifted_exist_quantify 
    (Sil.fav_from_list (node_get_dead node))
    (remove_temp_pvars dset node)

let do_symbolic_execution (node : node) (d:Prop.prop) =
  try
    let dset = Propset.propset_singleton d in
    let dset1 = 
      match node_get_kind node with
      | Prune_node (sil,e) -> 
          let dset' = exe_instrs dset sil in
	  let dset'' = SymExec.prune e dset' in
          E.log "@[<2>.... Prune ....@\n";
          E.log "EXP: %a@\n" Sil.pp_exp e;
          E.log "PROPSET:@\n";
          E.log "%a@\n@." Propset.pp_propset dset'';
          dset''          
      | Stmt_node sil | Return_Site_node sil -> 
	  exe_instrs dset sil
      | _ -> assert false in
    let dset2 = remove_temp_vars dset1 node in
    let dset3 = if converging_node node then Abs.lifted_abstract dset2 else dset2 in
    (*
    E.log "@[<2>....Result of execution....@\n";
    E.log "BEFORE:%a@\n@\n" Propset.pp_propset dset2;
    E.log "AFTER:%a@\n@." Propset.pp_propset dset3;
    *)
    dset3 
  with exn ->
    E.err "@[Failure of symbolic execution@.";
    E.err "@[<4>  NODE: %a@." Cfg_new.pp_node node;
    E.err "@[<4>  SIL INSTR:%a@." Sil.pp_instr_list (Cfg_new.node_get_sil node);
    raise exn

let target_call_time = ref 0.0

(* Does the symbolic execution for the initialization of function call. *)
let do_symbolic_execution_target_call 
    (caller_pdesc : proc_desc) (node : node)
    (callee_pdesc : proc_desc) (start : int) (d : Prop.prop) 
    : ((Ident.ident * Ident.ident) list * Prop.prop * Prop.prop) list =
  let initial_time = Stats.get_current_time () in
  let _ =
    E.log "@[.... Prelude for Procedure %s ....@\n@." (proc_desc_to_proc_name callee_pdesc) 
  in
  let callee_fundec = proc_desc_get_fundec callee_pdesc in
  let caller_aux_ids = 
    let proc_name = proc_desc_to_proc_name caller_pdesc in
    let summary = Proc.summary_find proc_name 
    in List.map fst (Proc.find_eqs summary start) in
  let ids = Locality.aux_vars_get_param callee_fundec in
  let callee_aux_ids = List.map fst ids in
  let param_temp_ids = List.map snd ids in
  let param_temp_exps = List.map (fun id -> Sil.Var id) param_temp_ids 
  in 
  let dset_param, offsets_args = 
    let instrs,args = match node_get_kind node with
      | Call_node (_,instrs,args) -> instrs,args
      | _ -> assert false in
    let ids = node_get_dead node in
    let dset = Propset.propset_singleton d in
    let dset' = doInstr2 dset ([],instrs) in 
    let root_args = List.map Sil.root_of_lexp (List.map fst args) in
    let offsets_args = List.map Sil.exp_get_offsets (List.map fst args) in
    let arg_fresh_exps = try
        List.combine root_args param_temp_exps
      with Invalid_argument _ -> 
        E.err "@[#### BUG: Parameter Mismatch ####@.";
        E.err "@[<4>  Proc: %s@." (proc_desc_to_proc_name callee_pdesc); 
        E.err "@[<4>  Actual Params: %a@." Sil.pp_exp_list root_args;
        E.err "@[<4>  Auxs: %a@." Sil.pp_exp_list param_temp_exps; 
        assert false in
    let f d = 
      let d' = List.fold_left (fun d (e,e') -> Prop.conjoin_eq e e' d) d arg_fresh_exps in
      let d'' = Prop.exist_quantify (Sil.fav_from_list ids) d'
      in d'' 
    in (Propset.propset_map f dset', offsets_args) 
  in
  let ds_split = 
    let globals = proc_desc_get_globals callee_pdesc in
    let f acc d = Locality.split callee_fundec globals param_temp_exps d :: acc 
    in Propset.propset_fold f [] dset_param
  in
  let do_frame (cutpoints_info, frame_d, nonframe_d) =
    let f cur_d (cutpoint_id,temp_id,e) = Prop.conjoin_eq (Sil.Var temp_id) e cur_d 
    in List.fold_left f frame_d cutpoints_info
  in
  let do_nonframe (cutpoints_info, frame_d, nonframe_d) = 
    let d_eqs = 
      let f cur_d (cutpoint_id,temp_id,e) = Prop.conjoin_eq (Sil.Var temp_id) e cur_d 
      in List.fold_left f nonframe_d cutpoints_info in
    let d_no_oldcuts = 
      let fav_caller_aux_ids = Sil.fav_from_list caller_aux_ids
      in Prop.exist_quantify fav_caller_aux_ids d_eqs in
    let d_formal_local_ret =
      let formal_decls =
	let construct_decl_init x y = 
	  (Sil.mk_pvar (Ident.string_to_name x.vname) callee_fundec "", Trans.trans_typ x.vtype, y) in
	let formals = proc_desc_get_formals callee_pdesc 
	in try 
            let f id offsets = 
              List.fold_left (fun e' offset -> 
                match offset with
                | Sil.Off_fld(fld) -> Sil.Lfield(e',fld)
                | Sil.Off_index(idx) -> Sil.Lindex(e',idx)) (Sil.Var id) offsets in
	    let callee_aux_vars = 
              List.map2 (fun id offsets -> 
                Some (f id offsets)) callee_aux_ids offsets_args in
	    List.map2 construct_decl_init formals callee_aux_vars 
	  with Invalid_argument _ -> 
            E.err "@[#### BUG: Parameter Mismatch ####@.";
            E.err "@[<4>  Proc: %s@." (proc_desc_to_proc_name callee_pdesc); 
            E.err "@[<4>  Number of Offset Lists: %d@." (List.length offsets_args);
            E.err "@[<4>  Number of Formals: %d@." (List.length formals);
            E.err "@[<4>  Number of Auxs: %d@." (List.length callee_aux_ids);
            assert false in
      let ret_local_decls =
	let construct_decl x = 
	  (Sil.mk_pvar (Ident.string_to_name x.vname) callee_fundec "", Trans.trans_typ x.vtype, None) in
	let locals = proc_desc_get_locals callee_pdesc in
	let local_decls = List.map construct_decl locals in
	let ret_var = ret_var_get_name callee_pdesc in
	let ret_type = ret_var_get_type callee_pdesc in
	let ret_decl = (ret_var, ret_type, None) 
	in ret_decl :: local_decls 
      in Prop.prop_init_formals_locals_seed formal_decls ret_local_decls d_no_oldcuts in
    let d_eqs' = 
      let aux_fresh_ids = try
          List.combine callee_aux_ids param_temp_ids
	with Invalid_argument _ -> 
	  assert false in
      let cut_temp_ids = 
	List.map (fun (cutpoint_id,temp_id,_) -> (cutpoint_id,temp_id)) cutpoints_info in
      let f d (id1,id2) = conjoin_eq (Sil.Var id1) (Sil.Var id2) d 
      in List.fold_left f d_formal_local_ret (aux_fresh_ids @ cut_temp_ids) in  
    let d_no_temps =
      let ids = List.map (fun (_,temp_id,_) -> temp_id) cutpoints_info in
      let fav_temp_ids = Sil.fav_from_list (ids@param_temp_ids)
      in Prop.exist_quantify fav_temp_ids d_eqs'
    in begin
      (* 
      E.log "@[<2>.... Non-Frame after Prologue ....@\n";
      E.log "%a@\n@." Prop.pp_prop d_no_temps;
       *)
      Abs.abstract d_no_temps 
    end
  in 
  let ds_split_res = 
    let f d_split =
      let (cutpoints_info,_,_) = d_split in
      let cuts_param = try
          List.combine callee_aux_ids param_temp_ids
	with Invalid_argument _ -> 
	  assert false in
      let cuts_noparam = 
	List.map (fun (cutpoint_id,temp_id,_) -> (cutpoint_id,temp_id)) cutpoints_info in
      let cuts = List.sort ident_pair_compare (cuts_param @ cuts_noparam)
      in (cuts, do_frame d_split, do_nonframe d_split) 
    in List.map f ds_split
  in 
    E.log "@[.... Finished Initialization and Splitting for Call to %s ....@\n@." 
      (proc_desc_to_proc_name callee_pdesc);
    target_call_time := !target_call_time +. (Stats.get_current_time () -. initial_time);
    ds_split_res

let ret_site_time = ref 0.0

(* Does a part of the symbolic execution for return sites, that can be done
 * without looking at frames. *)
let do_symbolic_execution_ret_site_noframe (callee_pdesc : proc_desc) 
    (eqs: (Ident.ident * Ident.ident) list) 
    (d: Prop.prop) : Propset.propset =
  let initial_time = Stats.get_current_time () in
  let fav_aux_ids = Sil.fav_from_list (List.map fst eqs) in
  let ret_name = ret_var_get_name callee_pdesc in
  let ret_type = ret_var_get_type callee_pdesc in
  let ret_temp = Locality.aux_vars_get_ret (Cfg_new.proc_desc_get_fundec callee_pdesc) in
  let dset_ret =
    let instr1 = Sil.Letderef (ret_temp,Sil.Lvar(ret_name),ret_type,Cil.locUnknown) in 
    let dset = Propset.propset_singleton d
    in 
    (* 
       E.log "@[<2>.... NoFrame in Epilogue (right before running *ret=..)....@\n";
       E.log "%a@\n@." Prop.pp_prop d; 
     *)
       doInstr2 dset ([], [instr1]) in
  let dset_res = 
    let dealloc_quantify dset_cur d =
      let d_removed = deallocate_locals_formals_ret callee_pdesc d in
      let d_eqs = 
	let add_eqs d0 (id1,id2) = Prop.conjoin_eq (Sil.Var id1) (Sil.Var id2) d0
	in List.fold_left add_eqs d_removed eqs in 
      let d_quantified = Prop.exist_quantify fav_aux_ids d_eqs in
      let d_renamed = Prop.prop_rename_primed_fresh d_quantified 
      in Propset.propset_add d_renamed dset_cur
    in Propset.propset_fold dealloc_quantify Propset.propset_empty dset_ret 
  in 
    ret_site_time := !ret_site_time +. (Stats.get_current_time () -. initial_time);
    dset_res

(* Does a part of the symbolic execution for return sites, that involves
 * frames. *) 
let combine_frame_and_dset (callee_pdesc : proc_desc) 
    (eqs : (Ident.ident * Ident.ident) list)
    (frame_d : Prop.prop) (dset: Propset.propset) : Propset.propset =
  let init_time = Stats.get_current_time () in
  let dset_combined = 
    let combine dset_cur d =
      match Locality.combine (Cfg_new.proc_desc_get_fundec callee_pdesc) frame_d d with
      | None -> dset_cur
      | Some d' -> Propset.propset_add d' dset_cur in
    Propset.propset_fold combine Propset.propset_empty dset in
  let cutpoints_fav = Sil.fav_from_list (List.map snd eqs) in
  let res = SymExec.lifted_exist_quantify cutpoints_fav dset_combined in
  (*
  E.log "@[<2>.... Existentially quantifying Props ....@\n";
  E.log "IDS:%a@\n@\n" Sil.pp_fav cutpoints_fav;
  E.log "BEFORE:@\n%a@\n@\n" Propset.pp_propset dset_combined; 
  E.log "AFTER:@\n%a@\n@." Propset.pp_propset res; 
  *)
  ret_site_time := !ret_site_time +. (Stats.get_current_time () -. init_time);
  res


(* ===================== END of symbolic execution ===================== *)



(* =============== START of rhs_forward_tabulate =============== *)

let propagate (start: start_info) (dset:Propset.propset) (curr_node: node) =
  let edgeset_todo = 
    let f edgeset_curr d = 
      EdgeSet.add (start, d) edgeset_curr 
    in Propset.propset_fold f EdgeSet.empty dset in
  let changed = path_edge_put_todo curr_node edgeset_todo
  in 
    (* E.log "@[.... Propagate: dset size : %d .....@\n@." (Propset.propset_size dset); *)
    if changed then ((* E.log "@[.... Work list: new item added ....@\n@."; *) work_list_add curr_node)

let propagate_singleton start (d:Prop.prop) curr_node =
  let dset = Propset.propset_singleton d 
  in propagate start dset curr_node   

(*
let get_called_proc_desc node = 
  let stmt = node_get_stmt node 
  in match node_get_kind node with
    | Call (pname, _, _, _) -> proc_name_to_proc_desc pname
    | _ -> assert false

let get_actual_params node = 
  let stmt = node_get_stmt node 
  in match stmt.skind with
    | Instr(Call(_,_,es,_):: _ ) -> es 
    | _ -> assert false
*)

let get_ret_site_node caller_node =
  let succ_nodes = node_get_succs caller_node
  in match succ_nodes with
    | [] -> assert false
    | [ret_site_node] -> ret_site_node
    | _ -> assert false
  
    
(* Does the propagation for the call nodes. That is, this propagation
 * deals with the case that curr_node belongs to Callp in the
 * algorithm *)
let do_call curr_node (start, curr_d) =
  E.log "@[**** Does the propagation for a call node ****@\n@.";
  let called_pdesc = match node_get_kind curr_node with
    | Call_node (called_pdesc,_,_) -> called_pdesc
    | _ -> assert false in
  let called_proc_name = proc_desc_to_proc_name called_pdesc in
  let caller_pdesc = node_get_proc_desc curr_node in
  let called_start_node = proc_desc_get_start_node called_pdesc in
  let called_summary = Proc.summary_find called_proc_name in
  let ret_site_node = match node_get_succs curr_node with
    | [ret_site_node] -> ret_site_node
    | _ -> assert false in
  let split_ds = 
    do_symbolic_execution_target_call 
      caller_pdesc curr_node
      called_pdesc start curr_d in
  let todo_propagate_d (eqs,frame_d,in_d) =
    (* cut point info., frame, reachable part *)
    let in_d_id = Proc.get_id called_summary in_d in 
    let f_ret_site _ =
      let dset = Proc.find called_summary in_d_id in
      let dset' = combine_frame_and_dset called_pdesc eqs frame_d dset in
      propagate start dset' ret_site_node in
    let f_called_proc _ = 
      propagate_singleton in_d_id in_d called_start_node in
    let f_obs_register _ =
      let obs = (start, curr_node, frame_d) 
      in Proc.add_obs called_summary in_d_id eqs obs
    in 
      f_ret_site ();
      f_called_proc ();
      f_obs_register () 
  in
    List.iter todo_propagate_d split_ds

(* Does the propagation when node is the exit node of a procedure *)
let do_exit exit_node edgeset_todo = 
  E.log "@[**** Does the propagation for an exit node ****@\n@.";
  let proc_desc = node_get_proc_desc exit_node in
  let proc_name = proc_desc_to_proc_name proc_desc in
  let proc_summary = Proc.summary_find proc_name in
  let do_noframe start dset =
    let eqs = Proc.find_eqs proc_summary start in
    let f dset_acc d =
      let dset' = do_symbolic_execution_ret_site_noframe proc_desc eqs d 
      in Propset.propset_union dset' dset_acc
    in Propset.propset_fold f Propset.propset_empty dset
  in 
  let do_join start dset =
    let old_dset = Proc.find proc_summary start in
    let delta_dset = Propset.propset_diff dset old_dset in
    let old_dset', delta_dset' =  
      if !Config.join_level >= 1 then Dom.propset_join old_dset delta_dset 
      else (old_dset, delta_dset) in
    let new_dset = Propset.propset_union old_dset' delta_dset' 
    in 
      Proc.replace proc_summary start new_dset;
      delta_dset'
  in 
  let do_frame start dset =
    if not (Propset.propset_is_empty dset) then
      begin
	let eqs = Proc.find_eqs proc_summary start in
	let todo (start, curr_node, frame_d) =
	  let succ_node = node_get_succs curr_node in  
	  let dset' = combine_frame_and_dset proc_desc eqs frame_d dset in
(*
	  let dset'' = do_symbolic_execution_ret_site proc_desc curr_node dset' in
*)
	  List.iter (propagate start dset') succ_node
	in 
	  Proc.notify proc_summary start todo 
      end
  in
    Imap.iter 
      (fun start new_dset ->
	let new_dset' = do_noframe start new_dset in
	let new_dset'' = do_join start new_dset' 
        in do_frame start new_dset'')
      (partition_edgeset edgeset_todo)


let do_join curr_node edgeset_todo =
  let curr_id = node_to_sid curr_node in
  let succ_nodes = node_get_succs curr_node in
  Imap.iter 
    (fun start new_dset ->
      let old_dset = Join_table.find curr_id start in
      let old_dset', new_dset' = Dom.propset_join old_dset new_dset in
      Join_table.put curr_id start 
	(Propset.propset_union old_dset' new_dset');
      List.iter (propagate start new_dset') succ_nodes)
    (partition_edgeset edgeset_todo)

let is_undefined_proc pdesc = 
  let fd = proc_desc_get_fundec pdesc in
  match fd.sbody.bstmts, fd.svar.vtype with
  | [], _ -> true
  | _, TFun (_,_,true,_) -> true
  | _, TFun _ -> false
  | _, _ -> assert false

module SkipProc = struct

  module Sset = Set.Make 
    (struct 
       type t = string
       let compare = Pervasives.compare
    end)

  let procs = ref Sset.empty

  let init () = procs := Sset.empty
  let add proc = procs := Sset.add proc !procs 
  let check proc = Sset.mem proc !procs 
      
end

let rhs_forward_tabulate () = 
  SkipProc.init ();
  while not (work_list_is_empty ()) do
    let curr_node = work_list_remove () in
    let kind_curr_node = node_get_kind curr_node in
    let sid_curr_node = node_to_sid curr_node in
    let proc_desc = node_get_proc_desc curr_node in
    let proc_name = proc_desc_to_proc_name proc_desc in
    let edgeset_todo = path_edge_checkout_todo curr_node in
    let succ_nodes = node_get_succs curr_node in
    E.log "@[**** Node: %i, Procedure: %s, Todo: %d ****@\n@." 
      sid_curr_node proc_name (EdgeSet.cardinal edgeset_todo); 
    match kind_curr_node with
    | Call_node (called_pdesc,instrs,_) -> 
        if (is_undefined_proc called_pdesc) then
          begin
            E.log "@[*** Does the propagation for a call node (undefined function) ****@.";
            let called_name = proc_desc_to_proc_name called_pdesc in
            if not (SkipProc.check called_name) then
              begin
                SkipProc.add called_name;  
                E.err "@[WARNING: Treat a call to %s by skip@." called_name
              end;
  	    EdgeSet.iter 
  	      (fun (start, curr_d) ->
                let dset = Propset.propset_singleton curr_d in
                let _ = doInstr2 dset ([],instrs) in  (* check dereferences in actual params *)
                let dset' = remove_temp_pvars dset curr_node in
	        List.iter (propagate start dset') succ_nodes)
	      edgeset_todo
          end
        else
          EdgeSet.iter (do_call curr_node) edgeset_todo
    | Exit_node _ ->
	if proc_name <> "main" then 
          begin
            do_exit curr_node edgeset_todo;
	    garbage_collect_summary curr_node
          end
    | Join_node -> do_join curr_node edgeset_todo
    | Stmt_node _ | Return_Site_node _ | Prune_node _ ->
	EdgeSet.iter 
	  (fun (start, curr_d) ->
	    let dset' = do_symbolic_execution curr_node curr_d in
	    List.iter (propagate start dset') succ_nodes)
	  edgeset_todo
    | Skip_node l when (!Config.join_level <= 1) && (l = "loop") ->
	EdgeSet.iter 
	  (fun (start, curr_d) ->
            let dset' = remove_temp_pvars (Propset.propset_singleton curr_d) curr_node in
            let dset'' = Abs.lifted_abstract dset' in
	    List.iter (propagate start dset'') succ_nodes)
	  edgeset_todo
    | Start_node _ | Skip_node _ ->
	EdgeSet.iter 
	  (fun (start, curr_d) ->
            let dset' = remove_temp_pvars (Propset.propset_singleton curr_d) curr_node in
	    List.iter (propagate start dset') succ_nodes)
	  edgeset_todo
  done;
  E.log "@[.... Work list empty. Stop ....@\n@." 

(* =============== END of rhs_forward_tabulate =============== *)






(* =============== START of rhs_get_initial_edge =============== *)

let allocate_locals_formals proc_desc d : Prop.prop =
  let fundec = proc_desc_get_fundec proc_desc in
  let formals = proc_desc_get_formals proc_desc in
  let locals = proc_desc_get_locals proc_desc in
  let construct_decl x = (Sil.mk_pvar (Ident.string_to_name x.vname) fundec "", Trans.trans_typ x.vtype, None) in
  let stack_alloc_formals = List.map construct_decl formals in
  let stack_alloc_locals = List.map construct_decl locals 
  in Prop.prop_init_formals_locals_seed stack_alloc_formals stack_alloc_locals d

(* TO DO: allocate global variables *)
let allocate_globals (f:Cil.file) (d:Prop.prop) : Prop.prop = 
  E.log "@[@\n#### Allocating global vars ####@.";
  List.fold_left (fun d' glob ->
    match glob with
    | GVar (vinfo,vinit,_) -> 
        begin
          let v_n = Ident.string_to_name vinfo.vname in
          let v_t = Trans.trans_typ vinfo.vtype in
          let v = Sil.mk_pvar_global v_n in  
          E.log "@[  Allocated Var: %s@." vinfo.vname;
          Prop.prop_init_global v v_t d'
        end
    | _ -> d') d f.globals


let rhs_get_initial_edge f =
  let main_name = "main" in
  let main_pdesc = 
    try
      Cfg_new.proc_name_to_proc_desc main_name 
    with Not_found -> 
      E.err "@[#### ERROR: cannot find main ####@\n@."; 
      assert false in
  let start_node = proc_desc_get_start_node main_pdesc in
  let init_data = allocate_locals_formals main_pdesc (Prop.prop_emp) in
  let init_data' = allocate_globals f init_data in
  let init_summary = Proc.summary_find main_name in
  let init_edge = Proc.get_id init_summary init_data', init_data' in
  start_node, init_edge
  
(* =============== END of rhs_get_initial_edge =============== *)




(* =============== START of rhs_collect_analysis_result =============== *)

(* Collect the analysis results for the exit node of main *)
let rhs_collect_analysis_result_main _ : Propset.propset =
  let pdesc = proc_name_to_proc_desc "main" in
  let exit_node = proc_desc_get_exit_node pdesc in
  let exit_sid = node_to_sid exit_node in
  let edge_list = path_edge_get_visited exit_sid in 
  let f dset (_, d) = Propset.propset_add d dset
  in List.fold_left f Propset.propset_empty edge_list

(* =============== END of rhs_collect_analysis_result =============== *)





(* ====================== START of rhs algorithm ====================== *)

let rhs_tabulate (f : Cil.file) = 
  let init_node, init_edge = rhs_get_initial_edge f in
  path_edge_reset ();
  work_list_add init_node;
  ignore (path_edge_put_todo init_node (EdgeSet.singleton init_edge));
  E.log "@[@\n#### Starting forward tabulation ####@\n@.";
  rhs_forward_tabulate ();
  Proc.display(); 
  rhs_collect_analysis_result_main ()

(* ====================== END of rhs algorithm ====================== *)




module ProcessTypeDecl : sig
  val doit : file -> unit
end = struct

  let tis = ref []
  let cis = ref []
  let ci_tags = ref []

  let reset' () = tis := []; cis := []; ci_tags := []
  let init' = reset' 
  let final' = reset'

  class visitor = object
    inherit nopCilVisitor
    method vglob = function 
    | GType(ti,_) -> 
        E.log "@[  Processing TypeDecl: GType@.";
        tis := ti::!tis;
        DoChildren
    | GCompTag(ci,_)  ->
        E.log "@[  Processing TypeDecl: GCompTag@.";
        cis := ci::!cis;
        DoChildren
    | GCompTagDecl(ci,_) ->
        E.log "@[  Processing TypeDecl: GCompTagDecl@.";
        ci_tags := ci::!ci_tags;
        DoChildren
    | GEnumTag _ ->
        E.log "@[  Processing TypeDecl: GEnumTag@.";
        DoChildren
    | GEnumTagDecl _ ->
        E.log "@[  Processing TypeDecl: GEnumTagDecl@.";
        DoChildren
    | GVarDecl _ ->
        E.log "@[  Processing TypeDecl: GVarDecl@.";
        DoChildren
    | GVar _ ->
        E.log "@[  Processing TypeDecl: GVar@.";
        DoChildren
    | GFun _ ->
        E.log "@[  Processing TypeDecl: GFun@.";
        DoChildren
    | GAsm _ ->
        E.log "@[  Processing TypeDecl: GAsm@.";
        DoChildren
    | GPragma _ ->
        E.log "@[  Processing TypeDecl: GPragma@.";
        DoChildren
    | GText _ -> 
        E.log "@[  Processing TypeDecl: GText@.";
        DoChildren
  end

  let update_cis' () =    
    let is_defined ci_tag =      
      List.exists (fun ci -> ci.cname = ci_tag.cname) !cis in    
    let is_undefined ci_tag =
      not (is_defined ci_tag) in
    let ci_tags' =      
      List.filter is_undefined !ci_tags in
    cis := ci_tags' @ !cis

  let doit (f:file) : unit =
    E.log "@[Translating CIL type decls into SIL type decls@.";
    init' ();
    visitCilFileSameGlobals (new visitor) f;
    update_cis' ();
    Trans.trans_typeinfo_decls !tis;
    Trans.trans_compinfo_decls !cis;
    final' ()
end

let feature : featureDescr = 
  let doit (f:file) =     
    ProcessTypeDecl.doit f;
    Cfg_new.compute_icfg f;
    Cfg_new.print_icfg_dotty []; 
    if !Config.liveness then Preanal.doit ();
    Global.doit ();
    let results = rhs_tabulate f 
    in begin
      E.err "@[.... Successfully Analyzed ....@\n@.";
      E.err "@[#### Final Results ####@\n@.";
      print_results results;
      Proc.display_stats();
      E.err "@[<2>#### Statistics ####@\n";
      E.err "Pre-analysis Time: %f@\n" (Preanal.gettime ());
      E.err "Join Time: %f@\n" !Dom.join_time;
      E.err "Time for Prelude of Proc Call: %f@\n" !target_call_time;
      E.err "Time for Epilogue of Proc Call: %f@\n@." !ret_site_time
    end
  in
    { fd_name = "interproc";
      fd_enabled = ref false;
      fd_description = "RHS interprocedural analysis";
      fd_extraopt = [
	"--arraylevel", Arg.Int (fun i -> Config.array_level := i),
        "the level of treating the array indexing and pointer arithmetic (default = 2)";
	"--joinlevel", Arg.Int (fun i -> Config.join_level := i),
	"the level of joining for interprocedural analysis (default = 3)";
	"--loclevel", Arg.Int (fun i -> Config.locality_level := i),
	"the level of applying the locality optimization (default = 1)";
        "--noliveness", Arg.Clear Config.liveness, 
        "turn the dead program variable elimination off";
        "--nelseg", Arg.Set Config.nelseg,
        "use only nonempty lsegs";
        "--absstruct", Arg.Int (fun i -> Config.abs_struct := i),
	"the level of abstracting fields of structs (default = 1)";
        "--absval", Arg.Int (fun i -> Config.abs_val := i),
	"the level of abstracting expressions (default = 1)";
        "--gc_summaries", Arg.Int (fun i -> Config.gc_summaries := i),
	"the level of gc of summaries at procedure exit (default = 1)";
	"--bound", Arg.Int (fun i -> Config.int_bound := i),
        "the bound for the integers (default = 100)";
	"--leak", Arg.Set Config.allowleak,
        "forget leaked cells during abstraction (default = false)";
      ];
      fd_doit = doit;
      fd_post_check = false } 
