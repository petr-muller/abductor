(*
 *
 * Copyright (c) 2006-2008,
 *  Cristiano Calcagno    <ccris@doc.ic.ac.uk>
 *  Dino Distefano        <ddino@dcs.qmul.ac.uk>
 *  Peter O'Hearn         <ohearn@dcs.qmul.ac.uk>
 *  Hongseok Yang         <hyang@dcs.qmul.ac.uk>
 * All rights reserved.
 *)

(** Interprocedural Footprint Analysis *)

open Ident
open Cil
open Cfg_new
open Sil
open Prop
open Fork
open Tabulation
module Exn = Exceptions
module Html = Error.Html
module F = Format
module DB = Error.DB

module E = Error.MyErr (struct let mode = Error.DEFAULT end)
(*let () = E.set_mode Error.ALWAYS
let () = E.set_colour Error.red*)

module IH = Inthash


(* Dotty printing for specs *)
let pp_speclist_dotty f (splist: spec list) = 
  Dotty.reset_proposition_counter ();
  Dotty.reset_dotty_spec_counter ();
  F.fprintf f "\n\n\ndigraph main { \nnode [shape=box]; \n";
  F.fprintf f "\n compound = true; \n";
(*  F.fprintf f "\n size=\"12,7\"; ratio=fill; \n"; *)
  List.iter (fun s -> Dotty.pp_dotty_one_spec f (Dom.jprop_to_prop s.pre) (s.post)) splist;
  F.fprintf f  "\n}" 

let pp_speclist_dotty_file filename spec_list =
  let outc = open_out (filename^ ".dot") in
  let fmt = F.formatter_of_out_channel outc in
  let () = F.fprintf fmt "#### Dotty version:  ####@.%a@.@." pp_speclist_dotty spec_list
  in close_out outc

let rec pp_speclist_in_separate_files filename specs n =
  match specs with
  | [] -> ()
  |one_spec::specs' -> pp_speclist_dotty_file (filename^"_"^string_of_int(n)) [one_spec];
      pp_speclist_in_separate_files filename specs' (n+1) 

let global_num= ref 0 

let pp_dotty_prop p = 
  global_num:=!global_num +1;
  let filename ="crappy_prop"^(string_of_int !global_num) in
  let outc = open_out (filename^ ".dot") in
  let fmt = F.formatter_of_out_channel outc in
(*  let _ =F.fprintf outc "#### Dotty version:  ####@.@.@." in*)
  let _ =F.fprintf fmt "\n\n\ndigraph main { \nnode [shape=box]; \n" in
  let _ =F.fprintf fmt "\n compound = true; \n" in
  let _ =Dotty.pp_dotty fmt (Dotty.Generic_proposition) p in
  let _ =F.fprintf fmt  "\n}" in
  close_out outc 



(* =============== START of the work_list object =============== *)    
  
module WorkList =
  Set.Make(struct
    type t = node
    let compare = node_compare 
  end)

let worklist : WorkList.t ref = ref WorkList.empty
let visited : WorkList.t ref = ref WorkList.empty

let visited_and_total_nodes () =
  let all_nodes = List.fold_right WorkList.add (get_all_nodes ()) WorkList.empty in
  let counted_nodes = WorkList.filter (function n -> match node_get_kind n with
    | Stmt_node _ | Prune_node _ | Call_node _ | Return_Site_node _ -> true
    | Start_node _ | Exit_node _ | Skip_node _ | Join_node -> false) all_nodes in
  let visited_nodes = WorkList.inter counted_nodes !visited
  in WorkList.elements visited_nodes, WorkList.elements counted_nodes

let work_list_reset () = worklist := WorkList.empty

let work_list_is_empty _ : bool =
  WorkList.is_empty !worklist

let work_list_add (node : node) : unit = 
  worklist := WorkList.add node !worklist

let work_list_remove _ : node =
  try 
    let min = WorkList.min_elt !worklist in
      if not !Config.footprint then (* make nodes visited during re-execution *)
	visited := WorkList.add min !visited;
      worklist := WorkList.remove min !worklist;
      min
  with Not_found -> begin
    E.err "@....Work list is empty! Impossible to remove edge...@."; 
    assert false
  end

let work_list_elements (filter : node -> bool) : node list =
  List.filter filter (WorkList.elements !worklist)

(* =============== END of the work_list object =============== *)


(* =============== START of the PathSet object =============== *)

(** Execution Paths *)
module Path : sig
  type t
  val contains : t -> t -> bool
  val curr_node : t -> node
  val start : node -> t
  val extend : node -> t -> t
  val join : t -> t -> t
  val pp : F.formatter -> t -> unit
  val iter : (t -> unit) -> t -> unit
  val write_to_cfg_file : t -> unit
end = struct
  type t = Pnothing | Pstart of node | Pnode of node * t | Pjoin of t * t
  let curr_node = function
    | Pnothing -> assert false
    | Pstart node -> node
    | Pnode (node,_) -> node
    | Pjoin _ -> assert false
  let start node = Pstart node
  let extend (node:node) path =
    if !Config.keep_path_info then Pnode (node,path)
    else Pnothing
  let join p1 p2 =
    if !Config.keep_path_info then Pjoin (p1,p2)
    else Pnothing
  let rec pp fmt = function
    | Pnothing -> ()
    | Pstart node -> F.fprintf fmt "%a" pp_node node
    | Pnode (node,path) -> F.fprintf fmt "%a.%a" pp path pp_node node
    | Pjoin (path1,path2) -> F.fprintf fmt "(%a + %a)" pp path1 pp path2
  let rec iter (f : t -> unit) (path:t) : unit = match path with
    | Pnothing -> ()
    | Pstart node -> f path
    | Pnode (node,p) ->
	iter f p;
	f path
    | Pjoin (p1,p2) ->
	iter f p1;
	iter f p2
  let rec contains p1 p2 = match p2 with
    | Pjoin (p2',p2'') ->
	contains p1 p2' || contains p1 p2''
    | _ -> p1==p2
  let get_edges p =
    let edges = ref [] in
    let rec go = function
      | Pnothing -> []
      | Pstart n -> [n]
      | Pnode(n,p) ->
	  let ns = go p in
	  let () = List.iter (fun n' -> edges := (n',n) :: !edges) ns
	  in [n]
      | Pjoin (p1,p2) ->
	  let ns1,ns2 = go p1, go p2
	  in ns1 @ ns2 in
    let _ = go p
    in !edges

  let write_to_cfg_file p =
    print_icfg_dotty (List.rev (get_edges p))
end

module PMap = Map.Make (struct
  type t = prop
  let compare = prop_compare end)

(* Set of (prop,path) pairs *)
module PathSet : sig
  type t
  val empty : t
  val elements : t -> Prop.prop list
  val filter : (prop -> bool) -> t -> t
  val union : t -> t -> t
  val diff : t -> t -> t
  val is_empty : t -> bool
  val add : Prop.prop -> Path.t -> t -> t
  val iter : (Prop.prop -> Path.t -> unit) -> t -> unit
  val fold : (prop -> Path.t -> 'a -> 'a) -> t -> 'a -> 'a
  val size : t -> int
  val pp : F.formatter -> t -> unit
  val d : t -> unit
  val filter_path : Path.t -> t -> prop list
end = struct
  type t = Path.t PMap.t

  let empty : t = PMap.empty

  let elements m =
    let plist = ref [] in
    let f prop path = plist := prop :: !plist in
    let ()  = PMap.iter f m
    in !plist

  let filter f ps =
    let elements = ref [] in
    let () = PMap.iter (fun p _ -> elements := p :: !elements) ps in
    let () = elements := List.filter (fun p -> not (f p)) !elements in
    let filtered_map = ref ps in
    let () = List.iter (fun p -> filtered_map := PMap.remove p !filtered_map) !elements
    in !filtered_map

  let add (p:prop) (path:Path.t) (map:t) : t =
    let path_new = try
	let path_old = PMap.find p map
	in Path.join path_old path
      with Not_found -> path
    in PMap.add p path_new map

  let union (map1:t) (map2:t) : t =
    PMap.fold add map1 map2

  let diff (map1:t) (map2:t) : t =
    let res = ref map1 in
    let rem p _ = res := PMap.remove p !res in
    let () = PMap.iter rem map2
    in !res

  let is_empty = PMap.is_empty

  let iter = PMap.iter

  let fold = PMap.fold

  let size map =
    let res = ref 0 in
    let add p _ = incr res in
    let () = PMap.iter add map
    in !res

  let pp fmt map =
    let count = ref 0 in
    let pp_path fmt path =
      if !Config.keep_path_info
      then F.fprintf fmt "[path: %a]" Path.pp path in
    let f prop path =
      incr count;
      F.fprintf fmt "PROP %d: %a@ @[%a@]@ " !count pp_path path pp_prop prop
    in iter f map

  let d (ps:t) = Error.add_print_action (Error.PTpathset, Obj.repr ps)

  let filter_path path map =
    let plist = ref [] in
    let f prop path' =
      if Path.contains path path'
      then plist := prop :: !plist
    in iter f map; !plist
end

module Shash = Inthash

module Join_table : sig
  val reset : unit -> unit
  val find : int -> PathSet.t
  val put : int -> PathSet.t -> unit
end = struct
  let table : PathSet.t Shash.t = Shash.create 1024
  let reset () = Shash.clear table
  let find i = 
    try Shash.find table i with Not_found -> PathSet.empty
  let put i dset = Shash.replace table i dset
end

let path_set_visited : PathSet.t Inthash.t = Inthash.create 1024

let path_set_todo : PathSet.t Inthash.t = Inthash.create 1024

let path_set_worklist_reset () = 
  Inthash.clear path_set_visited;
  Inthash.clear path_set_todo;
  Join_table.reset ();
  work_list_reset ()

let htable_retrieve (htable : PathSet.t Inthash.t) (key : int) : PathSet.t =
  try 
    Inthash.find htable key
  with Not_found ->
    Inthash.replace htable key PathSet.empty;
    PathSet.empty

let path_set_get_visited (sid:int) =
  let visited = htable_retrieve path_set_visited sid 
  in PathSet.elements visited

let path_set_visiting_check (node: node) : bool =
  match node_get_kind node with
  | Skip_node l when (!Config.join_level <= 1) && (Pervasives.(=) l "loop") -> true
  | Stmt_node _ | Prune_node _ | Skip_node _ -> false || !Config.keep_path_info
  | _ -> true

let path_set_put_todo (node: node) (d:PathSet.t) : bool =
  let sid = node_to_sid node in
  let old_todo = htable_retrieve path_set_todo sid in
  match path_set_visiting_check node with
  | false ->
      Inthash.replace path_set_todo sid (PathSet.union d old_todo);
      true
  | _ ->
      let old_visited = htable_retrieve path_set_visited sid in
      let d' = PathSet.diff d old_visited in 
      let todo_new = PathSet.union old_todo d' in
      Inthash.replace path_set_todo sid todo_new;
      not (PathSet.is_empty todo_new)

let path_set_checkout_todo (node: node) : PathSet.t = 
  try
    let sid = node_to_sid node in
    let todo = Inthash.find path_set_todo sid in
    Inthash.replace path_set_todo sid PathSet.empty;
    begin
      if path_set_visiting_check node then
	let visited = Inthash.find path_set_visited sid in
	let new_visited = PathSet.union visited todo in  
	Inthash.replace path_set_visited sid new_visited
    end;
    todo  
  with Not_found ->
    E.err "@.@.ERROR: could not find todo for node %a@.@." pp_node node;
    assert false

let path_set_is_empty_todo (sid:int) : bool = 
  try 
    let todo = Inthash.find path_set_todo sid 
    in PathSet.is_empty todo
  with Not_found ->
    false
(* =============== END of the edge_set object =============== *)

(** printing functions *)
let force_delayed_print fmt = function
  | (Error.PTstr,s) ->
      let s:string = Obj.obj s
      in F.fprintf fmt "%s" s
  | (Error.PTstrln,s) ->
      let s:string = Obj.obj s
      in F.fprintf fmt "%s@\n" s
  | (Error.PToff,off) ->
      let off:offset = Obj.obj off
      in pp_offset fmt off
  | (Error.PTpvar,pvar) ->
      let pvar:pvar = Obj.obj pvar
      in pp_pvar fmt pvar
  | (Error.PTloc,loc) ->
      let loc:Cil.location = Obj.obj loc
      in pp_loc fmt loc
  | (Error.PToff_list,offl) ->
      let offl:offset list = Obj.obj offl
      in pp_offset_list fmt offl
  | (Error.PTtyp_full,t) ->
      let t:typ = Obj.obj t
      in pp_typ_full fmt t
  | (Error.PTtexp_full,te) ->
      let te:exp = Obj.obj te
      in pp_texp_full fmt te
  | (Error.PTexp,e) ->
      let e:exp = Obj.obj e
      in pp_exp fmt e
  | (Error.PTexp_list,el) ->
      let el:exp list = Obj.obj el
      in pp_exp_list fmt el
  | (Error.PTatom,a) ->
      let a:atom = Obj.obj a
      in pp_atom fmt a
  | (Error.PTsexp,se) ->
      let se:strexp = Obj.obj se
      in pp_sexp fmt se
  | (Error.PThpred,hpred) ->
      let hpred:hpred = Obj.obj hpred
      in pp_hpred fmt hpred
  | (Error.PTtyp_list,tl) ->
      let tl:typ list = Obj.obj tl
      in (pp_seq pp_typ) fmt tl
  | (Error.PTsub,sub) ->
      let sub:subst = Obj.obj sub
      in pp_sub fmt sub
  | (Error.PTpi,pi) ->
      let pi:Sil.atom list = Obj.obj pi
      in pp_pi fmt pi
  | (Error.PTsigma,sigma) ->
      let sigma:Sil.hpred list = Obj.obj sigma
      in pp_sigma fmt sigma
  | (Error.PTprop,p) ->
      let p:prop = Obj.obj p
      in pp_prop fmt p
  | (Error.PTpropset,ps) ->
      let ps:Propset.propset = Obj.obj ps
      in Propset.pp_propset fmt ps
  | (Error.PTjprop_short,jp) ->
      let jp:Dom.joined_prop = Obj.obj jp
      in Dom.pp_jprop_short fmt jp
  | (Error.PTjprop_list,jpl) ->
      let jpl:Dom.joined_prop list = Obj.obj jpl
      in Dom.pp_jprop_list fmt jpl
  | (Error.PTinstr,i) ->
      let i:Sil.instr = Obj.obj i
      in pp_instr fmt i
  | (Error.PTinstr_list,il) ->
      let il:Sil.instr list = Obj.obj il
      in pp_instr_list fmt il
  | (Error.PTnode_instrs,b_n) ->
      let ((b:bool),(n:node)) = Obj.obj b_n
      in (pp_node_instr ~sub_instrs:b) fmt n
  | (Error.PTpathset,ps) ->
      let ps:PathSet.t = Obj.obj ps
      in Format.fprintf fmt "@[<v>%a@]@\n" PathSet.pp ps

(** hook up printer *)
let () = Error.force_delayed_print_ref := force_delayed_print


(* =============== START: Print a complete path in a dotty file =============== *)

let pp_path_dotty f path=
  let get_node_id_from_path p= 
    let node=Path.curr_node p 
    in Cfg_new.node_to_sid node
  in
  let count = ref 0 in
  let prev_n_id = ref 0 in
  let curr_n_id = ref 0 in
  prev_n_id:=-1;
  let g p =
    let curr_node = Path.curr_node p in
    let curr_path_set = htable_retrieve path_set_visited (node_to_sid curr_node) in
    let plist = PathSet.filter_path p curr_path_set in 
    incr count;
    curr_n_id:= (get_node_id_from_path p);
    Dotty.pp_dotty_prop_list f plist  !prev_n_id !curr_n_id;
    E.err "@.Path #%d: %a@." !count Path.pp p;
    prev_n_id:=!curr_n_id
  in
  E.err "@.@.Printing Path: %a to file error_path.dot@." Path.pp path;
  Dotty.reset_proposition_counter ();
  Dotty.reset_dotty_spec_counter ();
  F.fprintf f "\n\n\ndigraph main { \nnode [shape=box]; \n";
  F.fprintf f "\n compound = true; \n";
  F.fprintf f "\n size=\"12,7\"; ratio=fill; \n";
  Path.iter g path;
  F.fprintf f  "\n}" 

let pp_complete_path_dotty_file path = 
  let outc = open_out "error_path.dot" in
  let fmt = F.formatter_of_out_channel outc in
  let () = F.fprintf fmt "#### Dotty version:  ####@.%a@.@." pp_path_dotty path
  in close_out outc

(* =============== END: Print a complete path in a dotty file =============== *)

let num_procs = ref 0

let collect_do_abstract pset =
  if !Config.footprint then
    let () = Config.footprint := false in
    let pset' = Abs.lifted_abstract pset in
    let () = Config.footprint := true in
      pset'
  else Abs.lifted_abstract pset

let do_join_pre (pset: Propset.propset) =
  let plist = Propset.propset2proplist pset
  in
    if !Config.join_level > 0 then Dom.proplist_collapse_pre plist
    else List.map (fun p -> Dom.Prop p) plist

let do_join_post (pset: Propset.propset) =
  if !Config.join_level <= 0 then 
    pset
  else if !Config.spec_abs_level <= 0 then
    Dom.propset_collapse pset
  else 
    Dom.propset_collapse (Dom.propset_collapse_impl pset)

let do_meet_pre pset = 
  if !Config.meet_level > 0 then 
    Dom.propset_meet_generate pset
  else
    pset

(* Take the preconditions in the current spec table, apply join, and
   return the joined preconditions *)
let collect_preconditions proc_name : Dom.joined_prop list =
  let collect_do_abstract_one prop =
    if !Config.footprint then
      let () = Config.footprint := false in
      let prop' = Abs.abstract prop in
      let () = Config.footprint := true in
	prop'
    else Abs.abstract prop
  in
  let pres = List.map (fun spec -> Dom.jprop_to_prop spec.pre) (get_specs proc_name) in
  let pset = Propset.proplist2propset pres in
  let pset' =
    let f p =
      prop_normal_vars_to_primed_vars p
    in Propset.propset_map f pset in
  let () =
    E.d_strln ("#### Extracted footprint of " ^ proc_name ^ ":  ####");
    Propset.d_propset pset';
    E.d_ln () in
  let pset'' = collect_do_abstract pset' in
  let pset_meet = do_meet_pre pset'' in
  let () =
    E.d_strln ("#### Footprint of " ^ proc_name ^ " after Meet  ####");
    Propset.d_propset pset_meet;
    E.d_ln () in
  let jplist = do_join_pre pset_meet in
  let () =
    E.d_strln ("#### Footprint of " ^ proc_name ^ " after Join  ####");
    Dom.d_jprop_list jplist;
    E.d_ln () in
  let jplist' = 
    List.map (Dom.jprop_map prop_rename_primed_footprint_vars) jplist in
  let () =
    E.d_strln ("#### Renamed footprint of " ^ proc_name ^ ":  ####");
    Dom.d_jprop_list jplist';
    E.d_ln () in
  let jplist'' =
    let f p = prop_primed_vars_to_normal_vars (collect_do_abstract_one p)
    in List.map (Dom.jprop_map f) jplist' in
  let () =
    E.d_strln ("#### Abstracted footprint of " ^ proc_name ^ ":  ####");
    Dom.d_jprop_list jplist'';
    E.d_ln ()
  in jplist'' 


(** Add the summary to the table for the given function *)
let add_summary (proc_name : string) (summary:summary) : unit =
  E.err "Adding summary for %s@\n@[<v 2>  %a@]@." proc_name pp_summary summary;
  set_summary proc_name summary

(* =============== START of module Serialization =============== *)
module Serialization : sig
  val summary_get_env : summary -> NameEnv.t (** compute name environment from result *)
  val store_summary : string -> summary -> NameEnv.t -> unit (** Save result into the database *)
  val retrieve_specs : string -> bool (** Try to retrieve specs from tha database *)
end = struct
  let specs_filename pname = DB.absolute_path ["..";"specs";pname ^ ".specs"]

  let put (summ:summary) (nenv:NameEnv.t) =
    Obj.magic (summ,nenv)

  let get x =
    let ((summ:summary),(nenv:NameEnv.t)) = Obj.magic x
    in (summ,nenv)

  let summary_get_env summ =
    let nset = NameSet.create () in
    let () = summary_names_add nset summ in
    let nenv = NameSet.to_env nset
    in nenv

  let store_summary pname (summ:summary) (nenv:NameEnv.t) =
    let outc = open_out (specs_filename pname) in
    let () = Marshal.to_channel outc (put summ nenv) [];
    in close_out outc

  let retrieve_specs proc_name =
    try
      let inc = open_in (specs_filename proc_name) in
      let ((_summ:summary),(env:NameEnv.t)) = get (Marshal.from_channel inc) in
      let () = close_in inc
      in
	E.err "\nRetrieving specs of %s from file@." proc_name;
	let summ = summary_names_update env proc_name _summ in add_summary proc_name summ;
	true
    with
      | Sys_error s -> false
end
(* =============== END of module Serialization =============== *)


(** Perform phase transition from [FOOTPRINT] to [RE_EXECUTION] for a
    list of procs *)
let procs_perform_transition proc_names =
  let f proc_name =
    let joined_pres = collect_preconditions proc_name
    in transition_footprint_re_exe proc_name joined_pres
  in 
  List.iter f proc_names

let proc_is_undefined fd = 
  List.length fd.sbody.bstmts =0 

(** Try to read the spec from the db *)
let get_spec_from_db proc_name =
  !Config.incremental && Serialization.retrieve_specs proc_name

let should_be_skipped f =
  let proc_name = f.svar.vname in
  let () =
    if not (proc_exists proc_name) then
      ignore (get_spec_from_db proc_name)
  in if proc_is_undefined f && not (proc_exists proc_name) then
    (E.err "\n WARNING: Function %s is undefined.@." proc_name;
     (*
       let _ = Pretty.printf "\n    Type %a = "  d_type  f.svar.vtype in
       let _= Pretty.printf  "\n    Vstorage = %a \n   Returned non-deterministic value\n"  d_storage  f.svar.vstorage
     *) 
     if !Config.automatic_skip then true
     else raise Exn.Function_undefined)
    else false										 


(* =============== START of symbolic execution =============== *)
let converging_node node =
  let is_exit node = match node_get_kind node with
    | Exit_node _ -> true
    | _ -> false in
  let succ_nodes = node_get_succs node
  in
    List.exists is_exit succ_nodes
    || match succ_nodes with
    | [] -> false
    | [h] -> List.length (node_get_preds h) > 1
    | _ -> false

let exe_instrs dset instrl =
  let dset' = List.fold_left SymExec.lifted_sym_exec dset instrl in
  E.d_strln ".... After Symbolic Execution ....";
  Propset.d_propset dset';
  E.d_ln ();
  dset'

let remove_temp_pvars dset node =
  let instrl = Preanal.compile node (node_get_dead_pvar node)
  in if instrl!=[] then
    (E.d_strln ".... Translated Instrs to remove temp vars ....";
     Sil.d_instr_list instrl;
     E.d_ln ();
     exe_instrs dset instrl)
    else dset

let remove_temp_vars dset node =
  SymExec.lifted_exist_quantify 
    (fav_from_list (node_get_dead node))
    (remove_temp_pvars dset node)

(* Last node seen in symbolic execution *)
let last_node = ref dummy_node
let last_session = ref 0

exception Timeout_exe

(* propagate a set of results to the given node *)
let propagate (dset:Propset.propset) (path:Path.t) (curr_node: node) =
  let edgeset_todo =
    let f edgeset_curr d =
      PathSet.add d (Path.extend curr_node path) edgeset_curr
    in Propset.propset_fold f PathSet.empty dset in
  let changed = path_set_put_todo curr_node edgeset_todo
  in
    if changed then (work_list_add curr_node)

(* propagate a set of results to the set of nodes [dset], unless the set is empty and we're in footprint mode, in which case the current part of from_d is turned into an inconsistent prop, and propagated to the exit node *)
let propagate_nodes_divergence (proc_desc:proc_desc) (from_d:prop) (dset:Propset.propset) (path:Path.t) (nodes: node list) =
  if !Config.footprint && Propset.propset_is_empty dset then
    begin
      let exit_node = proc_desc_get_exit_node proc_desc in
      let exp_zero = Const_int 0 in
      let prop_incons = prop_replace_pi [Aneq (exp_zero,exp_zero)] (prop_replace_sigma [] from_d)
      in propagate (Propset.propset_singleton prop_incons) path exit_node
    end
  else List.iter (propagate dset path) nodes

let do_symbolic_execution (node : node) (d:prop) =
  let dset = Propset.propset_singleton d in
  let dset1 = 
    match node_get_kind node with
      | Prune_node (sil,e) -> 
          let dset' = exe_instrs dset sil in
	  let dset'' = SymExec.prune e dset' in
	    E.d_strln ".... Prune ....";
	    E.d_str "EXP: "; Sil.d_exp e; E.d_ln ();
            E.d_strln "PROPSET:";
	    Propset.d_propset dset'';
	    E.d_ln ();
            dset''
      | Stmt_node sil | Return_Site_node sil -> 
	  exe_instrs dset sil
      | Exit_node _ -> dset
      | _ -> assert false in
  let dset2 = remove_temp_vars dset1 node in
  let dset3 = if converging_node node then Abs.lifted_abstract dset2 else dset2
  in dset3

(* ===================== END of symbolic execution ===================== *)


(* Get the type of the return variable of procedure pdesc. *)
let ret_var_get_type (pdesc : proc_desc) : typ = 
  let cil_ret_type = proc_desc_get_cil_ret_type pdesc 
  in Trans.trans_typ cil_ret_type

let get_name_of_cilvar (curr_f : proc_desc) x = mk_pvar (string_to_name x.vname) (proc_desc_get_fundec curr_f) ""

let deallocate_locals (curr_f : proc_desc) p =
  let names_of_locals = List.map (get_name_of_cilvar curr_f) (proc_desc_get_locals curr_f)
  in prop_dispose_stack_proc p names_of_locals

let deallocate_formals (curr_f : proc_desc) p =
  let names_of_formals = List.map (get_name_of_cilvar curr_f) (proc_desc_get_formals curr_f)
  in prop_dispose_stack_proc p names_of_formals

let deallocate_ret (curr_f : proc_desc) (p:prop) (suffix:string) =
  let name_of_ret = proc_desc_get_cil_ret_var curr_f
  in prop_dispose_stack_proc p [(pvar_add_suffix name_of_ret suffix)]

let deallocate_locals_ret (curr_f : proc_desc) p =
  deallocate_locals curr_f (deallocate_ret curr_f p "")

let deallocate_locals_formals (curr_f : proc_desc) p =
  deallocate_locals curr_f (deallocate_formals curr_f p)

(* =============== START of forward_tabulate =============== *)

let do_join curr_node (edgeset_todo : PathSet.t) =
  let curr_id = node_to_sid curr_node in
  let succ_nodes = node_get_succs curr_node in
  let new_dset = edgeset_todo in
  let old_dset = Join_table.find curr_id in
  let old_dset', new_dset' =
    if !Config.footprint then old_dset,new_dset
    else old_dset,new_dset (* XXX join todo: Dom.propset_join old_dset new_dset *)
  in
    Join_table.put curr_id (PathSet.union old_dset' new_dset');
    List.iter (fun node ->
      PathSet.iter (fun prop path ->
	propagate (Propset.propset_singleton prop) path node)
	new_dset') succ_nodes

(* First, does the symbolic execution for the instructions "instrs".
 * Then, existentially quantifies all the identifiers in ids. Finally,
 * applies the abstraction. *)
let doInstr2 (p: prop) (ids, instrs): Propset.propset = 
  let () = E.d_strln ".... Executing Instuctions ...." in
  let post_dset = List.fold_left SymExec.lifted_sym_exec (Propset.propset_singleton p) instrs in
  let quantified_dset = SymExec.lifted_exist_quantify (fav_from_list ids) post_dset in    
  let new_dset = Abs.lifted_abstract quantified_dset 
  in 
    E.d_strln ".... After Symbolic Execution ....";
    Propset.d_propset new_dset; E.d_ln (); 
    new_dset

let prop_max_size = ref (0,prop_emp)
let prop_max_chain_size = ref (0,prop_emp)

(* Check if the prop exceeds the current max *)
let check_prop_size p path =
  let size = Metrics.prop_size p
  in if size > fst !prop_max_size then
    (prop_max_size := (size,p);
     E.d_strln ("Prop with new max size " ^ string_of_int size ^ ":");
     Prop.d_prop p;
     E.d_ln ())

(* If the prop seems to have a list which was not abstracted, return false *)
let filter_prop p =
  let size = Metrics.prop_chain_size p in
    if size > fst !prop_max_chain_size then
      (prop_max_chain_size := (size,p);
       E.d_strln ("Prop with new max chain size " ^ string_of_int size));
    if size > 300 then 
      let _ = pp_dotty_prop p
      in false 
    else true

(* Check prop size and filter out possible unabstracted lists *)
let check_prop_size edgeset_todo =
  if !Config.monitor_prop_size then PathSet.iter check_prop_size edgeset_todo

let apply_filtering (ps:PathSet.t) : PathSet.t =
  if !Config.filtering then PathSet.filter filter_prop ps
  else ps

let reset_prop_metrics () =
  prop_max_size := (0,prop_emp);
  prop_max_chain_size := (0,prop_emp)

let print_path path = 
  let count = ref 0 in
  let f p =
    let curr_node = Path.curr_node p in
    let curr_path_set = htable_retrieve path_set_visited (node_to_sid curr_node) in
    let plist = PathSet.filter_path p curr_path_set
    in 
      incr count;
      Propset.pp_proplist_dotty_file ("path" ^ (string_of_int !count) ^ ".dot") plist;
      E.err "@.Path #%d: %a@." !count Path.pp p;
      E.err "@[<v2>@,%a@,@[%a@]@]@." (pp_node_instr ~sub_instrs:true) curr_node Propset.pp_proplist plist
  in
    E.err "@.@.Path:@.%a@.@." Path.pp path;
    pp_complete_path_dotty_file path;
    Path.write_to_cfg_file path;
    Path.iter f path

module Logstring : sig
  val get_count : string -> int
  val get_log_string : string -> string
end = struct
  module StringMap = Map.Make (struct
    type t = string
    let compare (s1:string) (s2:string) = Pervasives.compare s1 s2 end)

  let count = ref 0
  let map = ref StringMap.empty

  let get_count proc_name =
    try
      StringMap.find proc_name !map
    with Not_found ->
      incr count;
      map := StringMap.add proc_name !count !map;
      !count

  let get_log_string proc_name =
    let phase_string = (if get_phase proc_name == FOOTPRINT then "FP" else "RE") in
    let timestamp = get_timestamp proc_name
    in F.sprintf "[%d/%d %s:%d] %s" (get_count proc_name) !num_procs phase_string timestamp proc_name
end

exception RE_EXE_ERROR

let forward_tabulate () =
  let do_call_node called_pdesc etl loc exe_iter instrs curr_node succ_nodes edgeset_todo =
    let fd = proc_desc_get_fundec called_pdesc in
    let proc_name = proc_desc_to_proc_name called_pdesc in
    let formal_types = List.map (fun v -> Trans.trans_typ v.vtype) fd.sformals in
    let do_one_call pre =
      if should_be_skipped fd then [pre]
      else
	let epl =
	  let actual_params =
	    (* Actual parameters are associated to their formal
	       parameter type if there are enough formal parameters, and
	       to their actual type otherwise. The latter case happens
	       with variable-arguments functions *)
	    let rec comb etl tl = match etl,tl with
	      | (e,t_e)::etl',t::tl' -> (e,t) :: comb etl' tl'
	      | etl,[] ->
		  if etl!=[] then
		    begin
		      E.err "WARNING: likely use of variable-arguments function\n";
		      (*
			E.err "actual parameters: %a@." pp_exp_list (List.map fst etl);
			E.err "formal parameters: %a@." (pp_seq pp_typ) formal_types;
		      *)
		    end;
		  etl
	      | [],_::_ ->
		  E.d_strln ("**** ERROR: Procedure " ^ ((proc_desc_get_fundec called_pdesc).svar.vname) ^ " mismatch in the number of parameters ****");
		  E.d_str "actual parameters: "; Sil.d_exp_list (List.map fst etl);
		  E.d_ln ();
		  E.d_str "formal parameters: "; Sil.d_typ_list formal_types;
		  E.d_ln ();
		  raise Exn.Wrong_argument_number
	    in comb etl formal_types in
	    try 
	      exe_function_call proc_name actual_params pre
	    with 
	      | Exn.Possible_memory_fault p when
		    begin
		      E.d_strln "Failure of symbolic execution: possible memory violation";
		      E.d_str "  Proposition:"; Prop.d_prop p; E.d_ln ();
		      false
		    end ->
		  assert false
	      | Exn.Memory_fault_Inconsistent_CallingState_MissingFP p when
		    begin
		      E.d_strln "Failure of symbolic execution: possible memory violation due to incompatibility of calling state and missing footprint";
		      E.d_str "  Proposition: "; Prop.d_prop p; E.d_ln ();
		      false
		    end ->
		  assert false
	in
	let exe_assign_return p =
	  let ret_temp = Locality.aux_vars_get_ret (proc_desc_get_fundec called_pdesc) in
	  let ret_name = pvar_add_suffix (proc_desc_get_cil_ret_var called_pdesc) Config.callee_suffix in
	  let ret_type = ret_var_get_type called_pdesc in
	  let instr1 = Letderef (ret_temp,Lvar(ret_name),ret_type,Cil.locUnknown) in 
	  let dlist = Propset.propset2proplist (doInstr2 p ([], [instr1]))
	  in List.map (fun p -> deallocate_ret called_pdesc p Config.callee_suffix) dlist
	in List.flatten (List.map exe_assign_return epl)
    in
      exe_iter
	(fun curr_d path ->
	  let dset = doInstr2 curr_d ([],instrs) in
	  let () = d_node_instrs ~sub_instrs:false curr_node in
	  let results = List.flatten (List.map do_one_call (Propset.propset2proplist dset)) in
	  let results' = remove_temp_vars (Propset.proplist2propset results) curr_node
	  in propagate_nodes_divergence (node_get_proc_desc curr_node) curr_d results' path succ_nodes)
	edgeset_todo
  in

  let do_before_node node session =
    let node_id = node_to_sid node in
    let loc = node_get_loc node in
    let proc_desc = node_get_proc_desc node in
    let proc_name = proc_desc_to_proc_name proc_desc
    in
      last_node := node;
      last_session := session;
      Error.reset_delayed_prints ();
      if Error.start_node node_id loc proc_name (List.map node_to_sid (node_get_preds node)) (List.map node_to_sid (node_get_succs node))
      then E.err "%a@\n@[<v>%a@]%a@\n" Html.pp_start_listing () (pp_node_instr ~sub_instrs:true) node Html.pp_end_listing ();

      E.err "%a%a" Html.pp_hline () (Html.pp_session_link ~with_name:true [".."]) (node_id,session,loc.Cil.line);
      E.err "<LISTING>@."
  in

  let do_after_node node =
    if !Config.test==false then Error.force_delayed_prints ()
    else Error.reset_delayed_prints ();
    E.err "</LISTING>@.";
    Error.finish_node (node_to_sid node)
  in
    
    while not (work_list_is_empty ()) do
      let curr_node = work_list_remove () in
      let kind_curr_node = node_get_kind curr_node in
      let sid_curr_node = node_to_sid curr_node in
      let proc_desc = node_get_proc_desc curr_node in
      let proc_name = proc_desc_to_proc_name proc_desc in
      let session =
	let session_ref = (get_summary proc_name).sessions in
	let () = incr session_ref
	in !session_ref in
      let () = Stats.time "do_before_node" (do_before_node curr_node) session in
      let edgeset_todo = apply_filtering (path_set_checkout_todo curr_node) in
      let succ_nodes = node_get_succs curr_node in
      let exe_iter f pathset =
	let exe prop path =
	  try f prop path with
	    | exe when !Config.keep_path_info ->
		E.err "Exception detected -- printing path@.";
		print_path path;
		raise exe
	in PathSet.iter exe pathset in
      let doit () =
	check_prop_size edgeset_todo;
	E.err "%s@\n" ("**** " ^ (Logstring.get_log_string proc_name) ^ " Node: " ^ string_of_int sid_curr_node ^ ", Procedure: " ^ proc_name ^ ", Session: " ^ string_of_int session ^ ", Todo: " ^ string_of_int (PathSet.size edgeset_todo) ^ " ****");
        PathSet.d edgeset_todo;
	E.d_strln ".... Instructions: .... ";
	Cfg_new.d_node_instrs ~sub_instrs:true curr_node;
	E.d_ln ();
	
	match kind_curr_node with
	  | Call_node (called_pdesc,instrs,etl) ->
	      (try do_call_node called_pdesc etl (node_get_loc curr_node) exe_iter instrs curr_node succ_nodes edgeset_todo with
		| Exn.Function_undefined -> ()
	      )
	  | Join_node -> do_join curr_node edgeset_todo
	  | Stmt_node _ | Return_Site_node _ | Prune_node _ | Exit_node _ ->
	      exe_iter 
		(fun curr_d path ->
		  let dset' = do_symbolic_execution curr_node curr_d in
		    propagate_nodes_divergence proc_desc curr_d dset' path succ_nodes)
		edgeset_todo
	  | Skip_node l when (!Config.join_level <= 1) && (Pervasives.(=) l "loop") ->
	      exe_iter 
		(fun curr_d path ->
		  let dset' = remove_temp_pvars (Propset.propset_singleton curr_d) curr_node in
		  let dset'' = Abs.lifted_abstract dset' in
		    propagate_nodes_divergence proc_desc curr_d dset'' path succ_nodes)
		edgeset_todo
	  | Start_node _ | Skip_node _ ->
	      exe_iter 
		(fun curr_d path ->
		  let dset' = remove_temp_pvars (Propset.propset_singleton curr_d) curr_node in
		    propagate_nodes_divergence proc_desc curr_d dset' path succ_nodes)
		edgeset_todo
      in try
	  (doit();
	   Stats.time "do_after_node" do_after_node curr_node)
	with
	  | exn when Exn.handle_exception exn ->
	      (match exn with
		| Exn.Leak _ ->
		    E.err "Failure of symbolic execution@.";
		    E.err "@[<4>  NODE: %a@]@." pp_node curr_node;
		    E.err "@[<4>  SIL INSTR:%a@]@." (pp_node_instr ~sub_instrs:true) curr_node
		| Exn.Possible_memory_fault (prop:Prop.prop) ->
		    E.err "Failure of symbolic execution: possible memory violation@.";
		    E.err "@[<4>  NODE: %a@]@." pp_node curr_node;
		    E.err "@[<4>  SIL INSTR:%a@]@." (pp_node_instr ~sub_instrs:true) curr_node;
		    E.err "@[<4>  Proposition:%a@]@." pp_prop prop
		| _ -> ());
	      Exn.log_exception (node_get_loc !last_node) (node_to_sid !last_node) !last_session exn;
	      Error.force_delayed_prints ();
	      Stats.time "do_after_node" do_after_node curr_node;
	      if not !Config.footprint then raise RE_EXE_ERROR
    done;
    E.d_strln ".... Work list empty. Stop ...."

let get_initial_node f =
  let proc_name = f.svar.vname in
  let pdesc = 
    try
      proc_name_to_proc_desc proc_name 
    with Not_found -> 
      E.err "#### ERROR: cannot find %s ####@.@." proc_name; 
      assert false in
  let start_node = proc_desc_get_start_node pdesc
  in start_node

(* Collect the analysis results for the exit node *)
let collect_analysis_result pdesc : Propset.propset =
  let exit_node = proc_desc_get_exit_node pdesc in
  let exit_sid = node_to_sid exit_node in
  let edge_list = path_set_get_visited exit_sid in 
  let f dset d = Propset.propset_add d dset
  in List.fold_left f Propset.propset_empty edge_list

module Pmap = Map.Make (struct type t = prop let compare = prop_compare end)

(* Extract specs from the result of footprint analysis *)
let extract_specs pdesc pset : spec list =
  let sub =
    let fav = fav_new () in
    let () = Propset.propset_iter (fun p -> prop_fav_add fav p) pset in
    let sub_list = List.map (fun id -> (id,Var (create_fresh_normal_ident (ident_name id)))) (fav_to_list fav)
    in sub_of_list sub_list in
  let pre_post_list =
    let plist = Propset.propset2proplist pset in
    let f p =
      let p' = deallocate_locals_formals pdesc p in
      (* let () = E.err "@.BEFORE abs:@.$%a@." pp_prop p' in *)
      let p'' = Abs.abstract p' in
      (* let () = E.err "@.AFTER abs:@.$%a@." pp_prop p'' in *)
      let pre,post = prop_extract_spec p''
      in (prop_sub sub pre, if Prover.check_inconsistency_base p then None else Some (prop_sub sub post))
    in List.map f plist in
  let pre_post_map =
    let add map (pre,post) =
      let current_posts = try Pmap.find pre map with Not_found -> Propset.propset_empty in
      let posts = match post with
	| None -> current_posts
	| Some post -> Propset.propset_add post current_posts
      in Pmap.add pre posts map
    in List.fold_left add Pmap.empty pre_post_list in
  let specs = ref [] in
  let add_spec pre posts =
    let posts' = List.map prop_remove_seed_vars (Propset.propset2proplist (do_join_post posts))
    in specs := {pre=Dom.Prop pre;post=posts'} :: !specs
  in Pmap.iter add_spec pre_post_map; !specs

let collect_postconditions pdesc : Propset.propset =
  let proc_name = proc_desc_to_proc_name pdesc in
  let pset = Propset.propset_map (deallocate_locals_formals pdesc) (collect_analysis_result pdesc) in
    E.d_strln ("#### [FUNCTION " ^ proc_name ^ "] Analysis result ####");
    Propset.d_propset pset;
    E.d_ln ();

    let res = try do_join_post (collect_do_abstract pset)
      with
        | exn when (match exn with Exn.Leak _ -> true | _ -> false) ->
	    raise (Failure "Leak in post collecion")
    in
      E.d_strln ("#### [FUNCTION " ^ proc_name ^ "] Postconditions after join ####");
      Propset.d_propset res;
      E.d_ln ();
      res

(** Construct an initial prop by extending [prop] with locals and formals *)
let initial_prop (curr_f: proc_desc) prop =
  let construct_decl x =
    (mk_pvar (string_to_name x.vname) (proc_desc_get_fundec curr_f) "", Trans.trans_typ x.vtype, None) in
  let formals =
    if !Config.footprint
    then List.map construct_decl (proc_desc_get_formals curr_f)
    else [] in (** formals already there in re-execution *)
  let locals =
    let ret_type = ret_var_get_type curr_f in
    let ret_var = (proc_desc_get_cil_ret_var curr_f, ret_type, None)
    in ret_var :: List.map construct_decl (proc_desc_get_locals curr_f)
  in prop_init_formals_locals_seed formals locals prop

(** Re-execute one precondition and return some spec if there was no
    re-execution error. *)
let execute_filter_prop pdesc init_node (precondition : Dom.joined_prop) : spec option =
  let proc_name = proc_desc_to_proc_name pdesc in
    E.d_strln ("#### Start: RE-execution for " ^ proc_name ^ " ####");
    E.d_str "Precond: "; Dom.d_jprop_short precondition;
    E.d_ln ();
    let init_prop = initial_prop pdesc (Dom.jprop_to_prop precondition) in
    let init_edgeset = PathSet.add init_prop (Path.start init_node) PathSet.empty in 
      try
	path_set_worklist_reset ();
	work_list_add init_node;
	ignore (path_set_put_todo init_node init_edgeset);
	forward_tabulate ();
	E.d_strln ("#### Finished: RE-execution for " ^ proc_name ^ " ####");
	E.d_str "Precond: "; Prop.d_prop (Dom.jprop_to_prop precondition);
	E.d_ln ();
	let posts = List.map prop_remove_seed_vars (Propset.propset2proplist (collect_postconditions pdesc)) in
	let pre =
	  let p = deallocate_locals_ret pdesc (Dom.jprop_to_prop precondition)
	  in match precondition with
	    | Dom.Prop _ -> Dom.Prop p
	    | Dom.Joined (_,jp1,jp2) -> Dom.Joined (p,jp1,jp2) in
	let spec = {pre=pre;post=posts}
	in Some spec
      with RE_EXE_ERROR -> 
	ignore(
          E.err "@[<2>#### [FUNCTION %s] ...ERROR" proc_name;
          E.err "when executing with the following:@\n";
          E.err "%a@\n" pp_prop (Dom.jprop_to_prop precondition);
          E.err "This precondition is filtered out.");
	None

(** get all the nodes in the current call graph with their dependents *)
let get_procs_and_dependents () =
  List.map (fun (n,ns) -> (n,StringSet.elements ns)) (CallGraph.get_nodes_and_dependents ())

(** Perform one phase of the analysis for a procedure *)
let perform_analysis_phase (f : Cil.fundec) : spec list =
  reset_prop_metrics ();
  Exn.reset_exn_log ();
  Abs.abs_rules_reset ();
  let init_node = get_initial_node f in
  let pdesc = node_get_proc_desc init_node in
  let proc_name = proc_desc_to_proc_name pdesc in

  let compute_footprint () : Propset.propset =
    let go () =
      let init_prop = initial_prop pdesc prop_emp in
      let init_edgeset = PathSet.add init_prop (Path.start init_node) PathSet.empty in
	E.err "@.#### [%d/%d] Start: Footprint Computation for %s ####@." (Logstring.get_count proc_name) !num_procs proc_name;
	E.d_strln "##### init_prop ="; Prop.d_prop init_prop; E.d_ln ();
	path_set_worklist_reset ();
	work_list_add init_node;
	ignore (path_set_put_todo init_node init_edgeset);
	forward_tabulate ();
	let results = Propset.propset_map (deallocate_locals_formals pdesc) (collect_analysis_result pdesc) in
	  E.err "@[#### [FUNCTION %s] ...OK #####@\n" proc_name;
	  E.err "#### Finished: Footprint Computation for %s ####@." proc_name;
	  E.d_strln ("#### [FUNCTION " ^ proc_name ^ "] Footprint Analysis result ####");
	  Propset.d_propset results; E.d_ln ();
	  results

    in (* Stats.time "find_pre's" *) go ()
  in

  let re_execution (candidate_preconditions: Dom.joined_prop list) : spec list =
    let go () =
      let filter p =
	execute_filter_prop pdesc init_node p
      in
	if !Config.undo_join then
	  Dom.jprop_filter filter candidate_preconditions
	else
	  let sp = List.map filter candidate_preconditions in
	  let sp' = List.filter (fun x -> x != None) sp in
	  let specs = List.map (function Some spec -> spec | None -> assert false) sp'
	  in specs
    in go ()
  in

    match get_phase proc_name with
      | FOOTPRINT ->
	  let footprint_results = compute_footprint () in
	  let specs = try extract_specs pdesc footprint_results with
            | Exn.Leak _ ->
		raise (Failure "Leak while collecting specs after footprint")
 in
	    (* E.stderr "Specs after footprint:@\n@[<v>%a@]@\n" pp_specs specs; *)
	    specs
      | RE_EXECUTION ->
	  let candidate_preconditions = List.map (fun spec -> spec.pre) (get_specs proc_name) in
	  let specs = re_execution candidate_preconditions in
	  let valid_preconditions = List.map (fun spec -> spec.pre) specs in
	  let filename =
	    let base = 
	      if not !Config.incremental then ""
	      else DB.absolute_path []
	    in Filename.concat base proc_name
	  in
	    if !Config.separate_dotty_specs then 
	      pp_speclist_in_separate_files filename specs 1
	    else
	      pp_speclist_dotty_file filename specs;
	    E.err "@.@.================================================";
	    E.err "@. *** CANDIDATE PRECONDITIONS FOR %s: " proc_name;
	    E.err "@.================================================@.";
	    E.err "@.%a @.@." Dom.pp_jprop_list candidate_preconditions;
	    E.err "@.@.================================================";
	    E.err "@. *** VALID PRECONDITIONS FOR %s: " proc_name;
	    E.err "@.================================================@.";
	    E.err "@.%a @.@." Dom.pp_jprop_list valid_preconditions;
	    specs

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
        E.d_strln "  Processing TypeDecl: GType";
        tis := ti::!tis;
        DoChildren
    | GCompTag(ci,_) ->
        E.d_strln "  Processing TypeDecl: GCompTag";
        cis := ci::!cis;
        DoChildren
    | GCompTagDecl(ci,_) ->
        E.d_strln "  Processing TypeDecl: GCompTagDecl";
        ci_tags := ci::!ci_tags;
        DoChildren
    | GEnumTag _ ->
        E.d_strln "  Processing TypeDecl: GEnumTag";
        DoChildren
    | GEnumTagDecl _ ->
        E.d_strln "  Processing TypeDecl: GEnumTagDecl";
        DoChildren
    | GVarDecl _ ->
        E.d_strln "  Processing TypeDecl: GVarDecl";
        DoChildren
    | GVar _ ->
        E.d_strln "  Processing TypeDecl: GVar";
        DoChildren
    | GFun _ ->
        E.d_strln "  Processing TypeDecl: GFun";
        DoChildren
    | GAsm _ ->
        E.d_strln "  Processing TypeDecl: GAsm";
        DoChildren
    | GPragma _ ->
        E.d_strln "  Processing TypeDecl: GPragma";
        DoChildren
    | GText _ -> 
        E.d_strln "  Processing TypeDecl: GText";
        DoChildren
  end

  let update_cis' () =
    let is_defined ci_tag = 
      List.exists (fun ci -> Pervasives.(=) ci.cname ci_tag.cname) !cis in
    let is_undefined ci_tag = 
      not (is_defined ci_tag) in
    let ci_tags' = 
      List.filter is_undefined !ci_tags in
    cis := ci_tags' @ !cis   

  let doit (f:file) : unit =
    E.d_strln "Translating CIL type decls into SIL type decls";
    init' ();
    visitCilFileSameGlobals (new visitor) f;
    update_cis' ();
    Trans.trans_typeinfo_decls !tis;
    Trans.trans_compinfo_decls !cis;
    final' ()
end

module Timeout : sig
  val exe_timeout : ('a -> 'b) -> 'a -> 'b option (* execute the function up to a given timeout in seconds *)
end = struct
  let set_alarm nsecs = 
    ignore (Unix.setitimer Unix.ITIMER_VIRTUAL {Unix.it_interval=0.0; Unix.it_value = float_of_int nsecs})
  let reset_alarm () =
    set_alarm 0
  let timeout_action _ =
    set_alarm 0;
    if !Config.filtering then
      (Config.filtering := false;
       raise Timeout_exe)
    else
      (Config.filtering := true;
       E.stderr "TIMEOUT: turning on filtering@.";
       set_alarm (!Config.timeout_re_exe))
  let () = Sys.set_signal Sys.sigvtalrm (Sys.Signal_handle timeout_action)
  let exe_timeout f x =
    try
      Config.filtering := false;
      set_alarm (Config.timeout());
      let res = f x in
      let () = reset_alarm ()
      in Some res
    with
      | Timeout_exe -> None
      | exe ->
	  reset_alarm ();
	  raise exe
end

module FundecSet = Set.Make(struct
  type t = Cil.fundec
  let compare fd1 fd2 = Pervasives.compare fd1.svar.vname fd2.svar.vname
end)

(** Analyze [proc_name] and return the updated summary. Use module
    [Timeout] to call [perform_analysis_phase] with a time limit, and
    then return the updated summary. Executed as a child process. *)
let analyze_proc proc_name : summary * NameEnv.t =
  let init_time = Stats.get_current_time () in
  let () = Config.footprint := match get_phase proc_name with
    | FOOTPRINT -> true
    | RE_EXECUTION -> false in
  let res = Timeout.exe_timeout perform_analysis_phase (Cfg_new.proc_desc_get_fundec (Cfg_new.proc_name_to_proc_desc proc_name)) in
  let elapsed = Stats.get_current_time () -. init_time in
  let prev_summary = get_summary proc_name in
  let new_summary = match res with
    | None ->
	let timestamp = max 1 (prev_summary.timestamp) in
	let () = Exn.exn_log_update_with_current prev_summary.stats.exn_log in
	let stats = {prev_summary.stats with stats_time = None} in
	let summ = {prev_summary with stats=stats; specs=[]; timestamp=timestamp} in
	  E.stderr "TIMEOUT:%fs@." elapsed;
	  summ
    | Some specs ->
	let normal_specs = List.map spec_normalize specs in
	let new_specs,changed = update_specs proc_name normal_specs in
	let timestamp = max 1 (prev_summary.timestamp + if changed then 1 else 0) in
	let stats_time = match prev_summary.stats.stats_time with
	  | None -> Some elapsed
	  | Some time -> Some (time +. elapsed) in
	let () = Exn.exn_log_update_with_current prev_summary.stats.exn_log in
	let stats = {prev_summary.stats with stats_time = stats_time} in
	let summ = {prev_summary with stats=stats; specs=new_specs; timestamp=timestamp} in
	  if normal_specs==[] then E.stderr "NO_SPECS:@."
	  else () (* E.stderr "...OK@." *);
	  summ in
  let env = Serialization.summary_get_env new_summary
  in (new_summary,env)

(** Process the result of the analysis of [proc_name]: update the
    returned summary and add it to the spec table. Executed in the
    parent process as soon as a child process returns a result. *)
let process_result (proc_name:string) ((_summ:summary),(env:NameEnv.t)) : unit =
  let summ = summary_names_update env proc_name {_summ with status=INACTIVE}
  in
    add_summary proc_name summ;
    procs_perform_transition (should_perform_transition proc_name);
    if !Config.incremental && not (summ.phase == FOOTPRINT) then
      Serialization.store_summary proc_name summ env;
    let procs_done = nodes_become_done proc_name in
      Fork.post_process_nodes procs_done

(** Return true if the analysis of [proc_name] should be
    skipped. Called by the parent process before attempting to analyze a
    proc. *)
let filter_out (proc_name:string) : bool =
  if !Config.re_analyze then false
  else
    let res = get_spec_from_db proc_name in
    let () = E.stderr "%s %s@." (Logstring.get_log_string proc_name) (if res then "READ_FROM_DB" else "")
    in res

let input_line inc = (* remove Line feed *)
  let linefeed = 13 in
  let line = Pervasives.input_line inc in
  let len = String.length line
  in if len>0 && Char.code (String.get line (len-1)) == linefeed
  then String.sub line 0 (len-1)
  else line

let create_exceptions_per_node exn_log =
  let exn_per_node = Hashtbl.create 17 in
  let add_exe node_id in_footprint exc_name =
    if in_footprint then
      try
	let set = Hashtbl.find exn_per_node node_id
	in Hashtbl.replace exn_per_node node_id (StringSet.add exc_name set)
      with Not_found ->
	Hashtbl.add exn_per_node node_id (StringSet.singleton exc_name)
  in Exn.exn_log_iter add_exe exn_log;
    exn_per_node

(** create exn message for html file *)
let create_exn_message exn_name =
 "\n<div class=\"msg\" style=\"margin-left:9ex\">" ^ exn_name ^ "</div>"

(** Create filename.c.html with line numbers and links to nodes *)
let write_file_log_html () =
  let nodes = get_all_nodes () in
  let tbl = Hashtbl.create 11 in
  let process_node n =
    let lnum = (node_get_loc n).Cil.line in
    let curr_nodes =
      try Hashtbl.find tbl lnum
      with Not_found -> []
    in Hashtbl.replace tbl lnum (n::curr_nodes) in
  let fname = Filename.basename !Config.curr_filename in
  let (fd,fmt) = Html.create ~with_background:false ["..";fname] in
  let cin = open_in !Config.curr_filename in
  let linenum = ref 0 in
  let global_exn_log = Exn.exn_log_empty () in
  let () = proc_iter (fun proc_name summary -> Exn.exn_log_update global_exn_log summary.stats.exn_log) in
  let exn_per_node = create_exceptions_per_node global_exn_log
  in
    List.iter process_node nodes;
    try
      (let s = "<center><h1>File " ^ !Config.curr_filename ^ "</h1></center>\n" ^
	"<table class=\"code\">\n"
	in F.fprintf fmt "%s" s);
      while true do
	let line = input_line cin in
	let () = incr linenum in
	let nodes_at_linenum =
	  try Hashtbl.find tbl !linenum
	  with Not_found -> [] in
	let exceptions_at_linenum =
	  let exns = ref [] in
	  let f node =
	    try exns := StringSet.elements (Hashtbl.find exn_per_node (node_to_sid node)) @ !exns
	    with Not_found -> () in
	    List.iter f nodes_at_linenum;
	    !exns in
	let linenum_str = string_of_int !linenum in
	let line_str = "LINE" ^ linenum_str in
	let str =
	  "<tr><td class=\"num\" id=\"" ^ line_str ^ "\">" ^ linenum_str ^ "</td><td class=\"line\">" ^ line
	in
	  F.fprintf fmt "%s" str;
	  List.iter (fun n -> Html.pp_node_link [fname] (get_node_description n) fmt (node_to_sid n)) nodes_at_linenum;
	  List.iter (fun n -> match node_get_kind n with
	    | Start_node proc_desc ->
		let proc_name = proc_desc_to_proc_name proc_desc in
		let num_specs = List.length (get_specs proc_name) in
		let label = proc_name ^ ": " ^ (string_of_int num_specs) ^ " specs"
		in Html.pp_proc_link [fname] proc_name fmt label
	    | _ -> ()) nodes_at_linenum;
	  List.iter (fun exn_name -> F.fprintf fmt "%s" (create_exn_message exn_name)) exceptions_at_linenum;
	  F.fprintf fmt "%s" "</td></tr>\n"
      done
    with End_of_file ->
      (F.fprintf fmt "%s" "</table>\n";
       close_in cin;
       Exn.pp_exn_log_html [fname] fmt global_exn_log;
       Html.close (fd,fmt))

(** Do footprint analysis *)
let doit (f:file) =
  let do_parallel = !Config.num_cores>1 || !Config.max_num_proc>0 in
  let init_time = Stats.get_current_time () in
  Config.footprint_analysis := true;
  ProcessTypeDecl.doit f;
  Stats.time "compute_icfg" compute_icfg f;
  Stats.time "print_icfg_dotty" print_icfg_dotty [];
  if !Config.liveness then Stats.time "preanal" Preanal.doit ();
  Stats.time "global" Global.doit ();
  DB.init();
  let all_fundecl = List.fold_right FundecSet.add (get_all_fundecs ()) FundecSet.empty in
  let defined_fundecl,undefined_fundecl = FundecSet.partition (fun fd -> CallGraph.node_defined fd.svar.vname) all_fundecl in
  let defined_procs = List.map (fun fd -> fd.svar.vname) (FundecSet.elements defined_fundecl) in
  let undefined_fundecl' = FundecSet.filter (fun fd ->
    not (proc_exists fd.svar.vname) && not (get_spec_from_db fd.svar.vname))
    undefined_fundecl in

  let () = num_procs := FundecSet.cardinal defined_fundecl in
  let num_undef_procs = FundecSet.cardinal undefined_fundecl' in
  let () = E.err "@.***** FOUND %d FUNCTIONS (%d undefined) *****@." !num_procs num_undef_procs in
  let () = E.err "@.Undefined functions:@." in
  let () =
    let pr_fundec fd = E.err "%s\n" fd.svar.vname
    in FundecSet.iter pr_fundec undefined_fundecl' in
  let () = E.err "@." in
  let () = E.stderr "@.***** FOUND %d FUNCTIONS (%d undefined) *****@." !num_procs num_undef_procs in
  let () =
    let fun_address_set = Trans.get_fun_address_set ()
    in E.err " Functions whose address has been taken: %a@." NameSet.pp fun_address_set in
  let do_analysis () =
    let procs_and_dependents = get_procs_and_dependents () in
    let () = List.iter init_summary procs_and_dependents in 
    (try Fork.parallel_iter_nodes analyze_proc process_result filter_out
      with exe when do_parallel ->
	E.err "@.@. ERROR exception raised in parallel execution@.";
	raise exe) in
  let () = Stats.time "footprint analysis" do_analysis () in
  let () = Stats.time "write log file" write_file_log_html () in
  let nvisited,ntotal = visited_and_total_nodes () in
      print_stats defined_procs (Stats.get_current_time () -. init_time) nvisited ntotal;
      Fork.print_timing ()

(** Feature description for footprint analysis *)
let feature : featureDescr =
  {fd_name = "footprint";
   fd_enabled = ref false;
   fd_description = "sil footprint analysis";
   fd_extraopt = [
     "--automatic_skip", Arg.Set Config.automatic_skip, "treat undefined functions as skip";
     "--one_spec_per_file", Arg.Set Config.separate_dotty_specs, "print only one spec per dot file";
     "--notest", Arg.Clear Config.test, "turn test mode off";
     "--test", Arg.Set Config.test, "turn test mode on";
     "--condensed_dotty", Arg.Set Config.condensed_dotty, "Print structs without danlging pointers";
     "--undo_join", Arg.Set Config.undo_join, "undo join of unsafe preconditions (default:false)";
     "--initial_heap_size", Arg.Int (fun i -> Config.set_minor_heap_size i), "set the initial size of the minor heap in Mb (default=1)";
     "--num_cores", Arg.Int (fun i -> Config.num_cores:=i), "set the number of cores to be used for parallel execution (default=1)";
     "--max_procs", Arg.Int (fun i -> Config.max_num_proc:=i), "set the maximum number of processes to be used for parallel execution (default=0)";
     "--join_cond", Arg.Int (fun i -> Config.join_cond:=i), "set the strength of the final information-loss check used by the join (default=1)";
     "--monitor_prop_size", Arg.Set Config.monitor_prop_size, "Monitor size of props and print every time max is exceeded";
     "--filtering", Arg.Set Config.filtering, "Filter out the props which seem to be coming from failure of list abstraction";
     "--keep_path_info", Arg.Int (fun i -> Config.keep_path_info := i<>0), "Keep path information if not zero (default=0)";
     "--timeout", Arg.Int (fun i -> Config.timeout_footprint := i; Config.timeout_re_exe := i), "set the timeout for each function in seconds (default=0)";
     "--timeout_footprint", Arg.Int (fun i -> Config.timeout_footprint := i), "set the timeout for the footprint phase (default=0)";
     "--timeout_re_exe", Arg.Int (fun i -> Config.timeout_re_exe := i), "set the timeout for re-execution phase (default=0)";
     "--incremental", Arg.Set Config.incremental, "turn on incremental mode: saves specs to directory db";
     "--re_analyze", Arg.Set Config.re_analyze, "re-analyze procedures even if the .spec file can be found in the db";
     "--meet_level", Arg.Int (fun i -> Config.meet_level:=i), "set the level of applying the meet operator (default=0)";
     "--splitting_fields_level", Arg.Int (fun i -> Config.splitting_fields_level:=i), "set the strictness of checks for the fields splitting model (default=0)";
     "--db_dir", Arg.String (fun s -> Config.db_dir:=s), "set the name of the db directory (default=/tmp/db)";
     "--current_filename", Arg.String (fun s -> Config.curr_filename:=s), "original name of the file we are analyzing";
     "--LOC", Arg.Int (fun i -> Config.loc:=i), "set the number of lines of the original file";
     "--set_pp_margin", Arg.Int (fun i -> F.set_margin i), "set right margin for the pretty printing functions";
     "--spec_abs_level", Arg.Int (fun i -> Config.spec_abs_level:=i), "set the level of abstracting the postconditions of discovered specs (default=1)";
   ];
   fd_doit = doit;
   fd_post_check = true;
  }
