(*
 *
 * Copyright (c) 2006-2008,
 *  Cristiano Calcagno    <ccris@doc.ic.ac.uk>
 *  Dino Distefano        <ddino@dcs.qmul.ac.uk>
 *  Peter O'Hearn         <ohearn@dcs.qmul.ac.uk>
 *  Hongseok Yang         <hyang@dcs.qmul.ac.uk>
 * All rights reserved.
 *)


open Ident
open Prop
open Cfg_new
module Exn = Exceptions

module E = Error.MyErr (struct let mode = Error.DEFAULT end)
module F = Format
module Html = Error.Html

(* =============== START of support for spec tables =============== *)
type spec = {pre: Dom.joined_prop; post: prop list}

type norm_spec = spec

(** Execution statistics *)
type stats =
    {stats_time: float option; exn_log: Exn.exn_log}

type status = ACTIVE | INACTIVE

type phase = FOOTPRINT | RE_EXECUTION

module StringMap = Map.Make (struct
  type t = string
  let compare (s1:string) (s2:string) = Pervasives.compare s1 s2 end)

type dependency_map_t = int StringMap.t

type summary =
    {sessions:int ref; (** Session number: how many nodes went trough symbolic execution *)
     timestamp:int; (** Timestamp of the specs, >= 0, increased every time the specs change *)
     status:status; (** ACTIVE when the proc is being analyzed *)
     phase:phase; (** in FOOTPRINT phase or in RE_EXECUTION PHASE *)
     dependency_map:dependency_map_t;  (** maps dependent procs to timestamp as last seen at the start of an analysys phase for this proc *)
     specs:norm_spec list;  (** list of specs *)
     stats:stats;  (** statistics: execution time and list of exceptions *)
    }

type spec_tbl = (string,summary) Hashtbl.t

let empty_stats () = {stats_time = Some 0.0; exn_log = Exn.exn_log_empty ()}

let spec_tbl: spec_tbl = Hashtbl.create 128

(** Return true if the proc is in the function table *)
let proc_exists proc_name =
  try
    ignore (Hashtbl.find spec_tbl proc_name);
    true
  with Not_found -> false

let get_summary proc_name =
  try Hashtbl.find spec_tbl proc_name
  with Not_found -> raise (Failure "Tabulation.find_summary: Not_found")

let get_status proc_name =
  (get_summary proc_name).status

let set_summary proc_name summary =
  Hashtbl.replace spec_tbl proc_name summary

let get_timestamp proc_name =
  (get_summary proc_name).timestamp

(** Return the specs for the proc in the spec table *)
let get_specs proc_name =
  try
    (Hashtbl.find spec_tbl proc_name).specs
  with Not_found -> raise (Failure "Tabulation.get_specs: Not_found")

(** Return the current phase for the proc *)
let get_phase proc_name =
  try
    (Hashtbl.find spec_tbl proc_name).phase
  with Not_found -> raise (Failure "Tabulation.get_phase: Not_found")

(** Set the current status for the proc *)
let set_status proc_name status =
  let summary = get_summary proc_name
  in set_summary proc_name {summary with status=status}

(** Create the initial dependency map with the given list of dependencies *)
let mk_initial_dependency_map proc_list : dependency_map_t =
  List.fold_left (fun map pname -> StringMap.add pname (-1) map) StringMap.empty proc_list

(** Re-initialize a dependency map *)
let re_initialize_dependency_map dependency_map =
  StringMap.map (fun dep_proc -> -1) dependency_map

(** Update the dependency map of [proc_name] with the current
    timestamps of the dependents *)
let update_dependency_map proc_name =
  let summary = get_summary proc_name in
  let current_dependency_map = StringMap.mapi (fun dep_proc old_stamp -> get_timestamp dep_proc) summary.dependency_map
  in set_summary proc_name {summary with dependency_map=current_dependency_map}

let rec post_equal pl1 pl2 = match pl1,pl2 with
  | [],[] -> true
  | [],_::_ -> false
  | _::_,[] -> false
  | p1::pl1',p2::pl2' ->
      if prop_equal p1 p2 then post_equal pl1' pl2'
      else false

(** [init_summary proc_name depend_list] initializes the summary for
    [proc_name] given dependent procs in list [depend_list]. Do nothing
    if a summary exists already *)
let init_summary (proc_name,depend_list) =
  let dependency_map = mk_initial_dependency_map depend_list in
  let summary =
    {sessions=ref 0;
     timestamp = 0;
     status = INACTIVE;
     phase = FOOTPRINT;
     dependency_map = dependency_map;
     specs = [];
     stats = empty_stats ()}
  in try
      ignore (Hashtbl.find spec_tbl proc_name)
    with Not_found ->
      Hashtbl.add spec_tbl proc_name summary

let summary_names_add nset (summ:summary) =
  let f {pre=pre;post=posts} =
    Dom.jprop_names_add nset pre;
    List.iter (prop_names_add nset) posts
  in List.iter f summ.specs

(** Take saved summary and name environment, and update names using the current environment *)
let summary_names_update (nenv:NameEnv.t) (pname:string) (summ:summary) : summary =
  let specs = summ.specs in
  let f {pre=pre;post=posts} =
    let pre' = Dom.jprop_names_update nenv pre in
    let posts' = List.map (prop_names_update nenv) posts
    in {pre=pre';post=posts'} in
  let specs' = List.map f specs
  in {summ with specs=specs'}

(** Iterate [f] on all the procs in the spec table *)
let proc_iter f =
  Hashtbl.iter f spec_tbl 

let pp_time fmt = function
  | None -> F.fprintf fmt "TIMEOUT"
  | Some t -> F.fprintf fmt "%f s" t

let pp_stats fmt stats =
  F.fprintf fmt "TIME:%a @," pp_time stats.stats_time;
  F.fprintf fmt "EXCEPTIONS: @[<h>%a@]" Exn.pp_exn_log stats.exn_log

(** Print the spec *)
let pp_spec fmt spec_entry =
  F.fprintf fmt "----------------------------------------------------------------@,";
  F.fprintf fmt "PRE:@,@[%a@]@," Dom.pp_jprop_short spec_entry.pre;
  F.fprintf fmt "POST:@,@[%a@]@," Propset.pp_proplist spec_entry.post; 
  F.fprintf fmt "----------------------------------------------------------------"

let pp_specs fmt specs =
  List.iter (fun spec -> F.fprintf fmt "%a@," pp_spec spec) specs

(** Print the decpendency map *)
let pp_dependency_map fmt dependency_map =
  let pp_entry fmt s n = F.fprintf fmt "%s=%d@ " s n
  in StringMap.iter (pp_entry fmt) dependency_map

let pp_summary_no_stats_specs fmt summary =
  F.fprintf fmt "Timestamp: %d@," summary.timestamp;
  F.fprintf fmt "Status: %s@," (if summary.status==ACTIVE then "ACTIVE" else "INACTIVE");
  F.fprintf fmt "Phase: %s@," (if summary.phase==FOOTPRINT then "FOOTRPRINT" else "RE_EXECUTION");
  F.fprintf fmt "Dependency_map: @[%a@]@," pp_dependency_map summary.dependency_map

(** Print the summary *)
let pp_summary fmt summary =
  pp_summary_no_stats_specs fmt summary;
  F.fprintf fmt "%a@," pp_stats summary.stats;
  F.fprintf fmt "%a" pp_specs summary.specs

let pp_stats_html fmt stats =
  Exn.pp_exn_log_html [] fmt stats.exn_log

let pp_summary_html fmt summary =
  Html.pp_start_listing fmt ();
  F.fprintf fmt "@[<v>%a@]" pp_summary_no_stats_specs summary;
  Html.pp_end_listing fmt ();
  pp_stats_html fmt summary.stats;
  Html.pp_hline fmt ();
  Html.pp_start_listing fmt ();
  F.fprintf fmt "@[<v>%a@]" pp_specs summary.specs;
  Html.pp_end_listing fmt ()

let pp_spec_table fmt () =
  Hashtbl.iter (fun proc_name summ -> F.fprintf fmt "PROC %s@\n%a@\n" proc_name pp_summary summ) spec_tbl

(** Print the stats for the given list of procedure names and given
    visited and total nodes *)
let print_stats procs tot_time nvisited ntotal =
  let node_filter n =
    let node_procname = proc_desc_to_proc_name (node_get_proc_desc n)
    in List.mem node_procname procs && proc_exists node_procname && get_specs node_procname != [] in
  let nodes_visited = List.filter node_filter nvisited in
  let nodes_total = List.filter node_filter ntotal in
  let num_proc = ref 0 in
  let num_ok_proc = ref 0 in
  let tot_specs = ref 0 in
  let num_timeout = ref 0 in
  let print_stats_proc proc_name res =
    if List.mem proc_name procs then
      begin
	incr num_proc;
	tot_specs := (List.length res.specs) + !tot_specs;
	if res.specs != [] then incr num_ok_proc;
	E.err "procedure %s: %d entries " proc_name (List.length res.specs);
	(match res.stats.stats_time with
	  | Some time ->
	      E.err "in %f sec@." time
	  | None ->
	      incr num_timeout;
	      E.err "TIMEOUT@.");
	E.err "%a@." Exn.pp_exn_log_and_extend_table res.stats.exn_log
      end in
  let print_file_stats fmt () =
(*    F.fprintf fmt "VISITED: %a@." (pp_seq pp_node) nodes_visited;
    F.fprintf fmt "TOTAL: %a@." (pp_seq pp_node) nodes_total; *)
    F.fprintf fmt "@.++++++++++++++++++++++++++++++++++++++++++++++++++@\n";
    F.fprintf fmt "+ FILE: %s  LOC: %n  COVERAGE: %d/%d)@\n" !Config.curr_filename !Config.loc (List.length nodes_visited) (List.length nodes_total);
    F.fprintf fmt "+  num_procs: %d (%d ok, %d timeouts, %d exceptions)@\n" !num_proc !num_ok_proc !num_timeout (Exn.exn_table_size_footprint ());
    F.fprintf fmt "+  exceptions: %a@\n"  Exn.pp_exn_table_stats ();
    F.fprintf fmt "+  time: %f@\n" tot_time;
    F.fprintf fmt "+  specs: %d@\n" !tot_specs;
    F.fprintf fmt "++++++++++++++++++++++++++++++++++++++++++++++++++@.";
    Exn.print_exn_table_details fmt;
 in
  let save_file_stats () =
    let filename = Filename.concat !Config.db_dir (Filename.basename !Config.curr_filename) ^ ".stats" in
    let outc = open_out filename in
    let fmt = F.formatter_of_out_channel outc in
    let () = print_file_stats fmt ()
    in close_out outc
  in
    E.err "Interprocedural footprint analysis terminated@.";
    proc_iter print_stats_proc;
    E.stderr "%a" print_file_stats ();
    if !Config.incremental then save_file_stats ()
(* =============== END of support for spec tables =============== *)


(* =============== START of module Process =============== *)
module Process : sig
  type t
  val kill_remaining_processes : unit -> unit
  val kill_process : t -> unit
  val get_pid : t -> int
  val spawn_fun : ((string*int) -> 'b) -> t
  val send_to_child : t -> (string*int) option -> unit
  val receive_from_child : unit -> t*'b
  val get_last_input : t -> (string*int)
end = struct


let shared_in,shared_out = (* shared channel from children to parent *)
  let (read,write) = Unix.pipe ()
  in Unix.in_channel_of_descr read, Unix.out_channel_of_descr write

type pipe_str =
    { p2c_in : in_channel;
      p2c_out : out_channel;
      c2p_in : in_channel;
      c2p_out : out_channel;
      mutable input : Obj.t;
      mutable pid : int }
  
type t = pipe_str

let processes = ref []

let get_pid p_str = p_str.pid

let send_to_child p_str v =
  match v with
    | None -> ()
    | Some x -> p_str.input <- (Obj.magic x);
  Marshal.to_channel p_str.p2c_out v [];
  flush p_str.p2c_out

let incr_process_count p_str =
  processes := p_str :: !processes
  (* ; F.printf "@.Number of processes: %d@." (List.length !processes) *)

let decr_process_count pid =
  processes := List.filter (fun p_str' -> pid != p_str'.pid) !processes
  (* ; F.printf "@.Number of processes: %d@." (List.length !processes) *)

let kill_process p_str =
  E.err "killing process %d@." p_str.pid;
  Unix.kill p_str.pid Sys.sigkill;
  Unix.close (Unix.descr_of_in_channel p_str.p2c_in);
  Unix.close (Unix.descr_of_out_channel p_str.p2c_out);
  Unix.close (Unix.descr_of_in_channel p_str.c2p_in);
  Unix.close (Unix.descr_of_out_channel p_str.c2p_out);
  ignore (Unix.waitpid [] p_str.pid);
  decr_process_count p_str.pid

let kill_remaining_processes () =
  E.err "@.%d remaining processes@." (List.length !processes);
  List.iter kill_process !processes

let receive_from_child () =
  let sender_pid = Marshal.from_channel shared_in in
  let p_str = (* find which process sent its pid on the shared channel *)
    try List.find (fun p_str -> p_str.pid = sender_pid) !processes
    with Not_found -> assert false
  in
    match Marshal.from_channel p_str.c2p_in with
      | None ->
	  E.err "@.@.ERROR: child process %d died. Stopping@.@." sender_pid;
	  decr_process_count sender_pid;
	  kill_remaining_processes ();
	  exit 0
      | Some x -> (p_str,x)

let receive_from_parent p_str =
  match Marshal.from_channel p_str.p2c_in with
    | Some n ->
        n
    | None ->
	(* F.printf "@._%d_ Received stop signal, now stopping%!@." p_str.cpid; *)
	exit(0)

let _send_to_parent (p_str:t) v =
  Marshal.to_channel shared_out p_str.pid []; (* tell parent I'm sending the result *)
  flush shared_out;
  Marshal.to_channel p_str.c2p_out v [];
  flush p_str.c2p_out

let send_to_parent (p_str:t) v =
  _send_to_parent p_str (Some v)

(* tell the parent that I'm about to exit *)
let send_exit_to_parent (p_str:t) =
  _send_to_parent p_str None

let get_last_input p_str =
  Obj.magic p_str.input

let spawn_fun service_f =
  let p_str = 
    let (p2c_read,p2c_write) = Unix.pipe () in
    let (c2p_read,c2p_write) = Unix.pipe () in
      (* Unix.set_nonblock c2p_read; *)
      { p2c_in = Unix.in_channel_of_descr p2c_read;
	p2c_out = Unix.out_channel_of_descr p2c_write;
	c2p_in = Unix.in_channel_of_descr c2p_read;
	c2p_out = Unix.out_channel_of_descr c2p_write;
	input = Obj.magic 0;
        pid = 0 } in
  let colour = Error.next_colour ()
  in match Unix.fork () with
    | 0 ->
	Config.in_child_process := true;
        p_str.pid <- Unix.getpid ();
	Error.change_terminal_colour colour;
	E.err "@.STARTING PROCESS %d@." p_str.pid;
	let rec loop () =
	  let n = receive_from_parent p_str in
	  let res = service_f n in
	    send_to_parent p_str res;
	    loop ()
	in
loop ()
(*
 (try loop () with exe ->
	  E.err "@.@.ERROR finished with exception@.@.";
	  send_exit_to_parent p_str;
	  raise exe (* exit 0 *))
*)
    | cid ->
	p_str.pid <- cid;
	incr_process_count p_str;
	p_str
end
(* =============== END of module Process =============== *)

let parallel_mode = ref false

(* =============== START of module Timing_log =============== *)
module Timing_log : sig
  val event_start : string -> unit
  val event_finish : string -> unit
  val print_timing : unit -> unit
end = struct
  type ev_kind = START | FINISH
  type event = {time : float; kind : ev_kind; name : string}

  let active = ref []
  let log = ref []
  let bogus_time = -1000.0
  let bogus_event = {time=bogus_time;kind=START;name=""}
  let last_event = ref bogus_event
  let initial_time = ref bogus_time
  let total_procs_time = ref 0.0
  let total_cores_time = ref 0.0


  let reset () =
    active := [];
    log := [];
    last_event := bogus_event;
    initial_time := bogus_time;
    total_procs_time := 0.0;
    total_cores_time := 0.0

  let expand_log event =
    let elapsed = event.time -. !last_event.time in
    let num_procs = List.length !active in
    let num_cores = min num_procs !Config.num_cores in
      match Pervasives.(=) !last_event bogus_event with
	| true ->
	    last_event := event;
	    initial_time := event.time;
	| false ->
	    let label =
	      List.fold_right (fun name s -> "\\n" ^ name ^s) !active "" in
	      log := (!last_event,label,event)::!log;
	      total_procs_time := (float_of_int num_procs) *. elapsed +. !total_procs_time;
	      total_cores_time := (float_of_int num_cores) *. elapsed +. !total_cores_time;
	      last_event := event

  let event_start s =
    expand_log {time=(Stats.get_current_time ()); kind=START; name=s};
    active := s :: !active

  let event_finish s =
    expand_log {time=(Stats.get_current_time ()); kind=FINISH; name=s};
    active := List.filter (fun s' -> s' != s) !active

  let print_timing () =
    let total_time = !last_event.time -. !initial_time in
    let avg_num_proc = !total_procs_time /. total_time in
    let avg_num_cores = !total_cores_time /. total_time in
    let pp_event fmt event = match event.kind with
      | START -> F.fprintf fmt "\"%fs START %s\"" event.time event.name
      | FINISH -> F.fprintf fmt "\"%fs FINISH %s\"" event.time event.name in
    let pp_edge fmt (event1,label,event2) =
      let color = match event1.kind with
	| START -> "green"
	| FINISH -> "red" in
      F.fprintf fmt "%a -> %a [label=\"{%fs}%s\",color=\"%s\"]\n" pp_event event1 pp_event event2 (event2.time -. event1.time) label color in
    let outc = open_out "timing.dot" in
    let fmt = F.formatter_of_out_channel outc in
      F.fprintf fmt "digraph {\n";
      List.iter (pp_edge fmt) !log;
      F.fprintf fmt "}@.";
      close_out outc;
      if !parallel_mode then E.stderr "@.Parallel timings:   total time %f  avg processes %f  avg cores %f@." total_time avg_num_proc avg_num_cores
end
(* =============== END of module Timing_log =============== *)

(** print the current call graphs as a dotty file () *)
let print_call_graph_dotty () =
  let outc = open_out "call_graph.dot" in
  let fmt = F.formatter_of_out_channel outc in
  let () = CallGraph.pp_graph_dotty fmt;
  in close_out outc

(** print the timing info for the processes *)
let print_timing () =
  Timing_log.print_timing ()

module WeightedStringSet = 
  Set.Make(struct
    type t = (string*int)
    let compare ((n1:string),(w1:int)) ((n2:string),(w2:int)) =
      let n = int_compare w1 w2 in if n != 0 then n
	else Pervasives.compare n1 n2
  end)

let pp_weightednodeset fmt set =
  let f (node,weight) = F.fprintf fmt "%s@ " node
  in WeightedStringSet.iter f set

let compute_weighed_nodes () =
  let nodeset = ref WeightedStringSet.empty in
  let add_weighted_node (n,w) =
    nodeset:= WeightedStringSet.add (n,w) !nodeset
  in
    List.iter add_weighted_node (CallGraph.get_weighted_nodes ());
    !nodeset

(* Return true if there is no proc dependent on [node] whose specs
   have changed since [node] was last analyzed *)
let node_is_up_to_date node =
  let summary = get_summary node in
  let filter dependent_proc = get_timestamp dependent_proc = StringMap.find dependent_proc summary.dependency_map in
  let res = StringSet.for_all filter (CallGraph.get_dependents node)
(*  in let () = E.stderr "node_is_up_to_date %s: %b@\n" node res *)
  in res

(** Return the list of procedures which should perform a phase
    transition from [FOOTPRINT] to [RE_EXECUTION] *)
let should_perform_transition proc_name : string list =
  let recursive_dependents = CallGraph.get_recursive_dependents proc_name in
  let recursive_dependents_plus_self = StringSet.add proc_name recursive_dependents in
  let should_transition =
    get_phase proc_name == FOOTPRINT &&
    StringSet.for_all node_is_up_to_date recursive_dependents &&
    StringSet.for_all (fun n -> get_status n == INACTIVE) recursive_dependents
  in if should_transition then StringSet.elements recursive_dependents_plus_self
    else []

(** Perform the transition from [FOOTPRINT] to [RE_EXECUTION] in spec table *)
let transition_footprint_re_exe proc_name joined_pres =
  let summary = get_summary proc_name in
  let summary' =
    {summary with
      timestamp = 0;
      phase = RE_EXECUTION;
      dependency_map = re_initialize_dependency_map summary.dependency_map;
      specs = List.map (fun jp -> {pre=jp;post=[]}) joined_pres
    }
  in set_summary proc_name summary'

module SpecMap = Map.Make (struct
  type t = Dom.joined_prop
  let compare = Dom.jprop_compare
end)

let spec_fav (spec:spec) : Sil.fav =
  let fav = Sil.fav_new () in
    Dom.jprop_fav_add fav spec.pre;
    List.iter (prop_fav_add fav) spec.post;
    fav

let spec_sub sub spec =
  {pre = Dom.jprop_sub sub spec.pre;
   post = List.map (prop_sub sub) spec.post}

(** Convert spec into normal form w.r.t. variable renaming *)
let spec_normalize (spec:spec) : spec =
  let fav = spec_fav spec in
  let idlist = Sil.fav_to_list_stable fav in
  let count = ref 0 in
  let sub = Sil.sub_of_list (List.map (fun id -> incr count; (id,Sil.Var (create_normal_ident (ident_name id) !count))) idlist)
  in spec_sub sub spec

(** Update the specs of the current proc after the execution of one phase *)
let update_specs proc_name new_specs : spec list * bool =
  let phase = get_phase proc_name in
  let old_specs = get_specs proc_name in
  let changed = ref false in
  let current_specs = ref (List.fold_left (fun map spec -> SpecMap.add spec.pre (Propset.proplist2propset spec.post) map) SpecMap.empty old_specs) in
  let re_exe_filter old_spec = (* filter out pres which failed re-exe *)
    if phase==RE_EXECUTION && not (List.exists (fun new_spec -> Dom.jprop_equal new_spec.pre old_spec.pre) new_specs)
    then
      (changed:=true;
       current_specs := SpecMap.remove old_spec.pre !current_specs)
    else ()
  in
  let add_spec spec = (* add a new spec by doing union of the posts *)
    try
      let old_post = SpecMap.find spec.pre !current_specs in
      let new_post = Propset.propset_union old_post (Propset.proplist2propset spec.post) in
	if Propset.propset_compare old_post new_post <> 0 then
	  (changed := true;
	   E.log "Specs changed: added new post %a@." Propset.pp_propset new_post;
	   current_specs := SpecMap.add spec.pre new_post (SpecMap.remove spec.pre !current_specs))
    with Not_found ->
      (changed := true;
       E.log "Specs changed: added new pre %a@." Dom.pp_jprop_short spec.pre;
       current_specs := SpecMap.add spec.pre (Propset.proplist2propset spec.post) !current_specs) in
  let res = ref [] in
  let convert pre post_set =
    res := {pre=pre; post=Propset.propset2proplist post_set} :: !res
  in
    List.iter re_exe_filter old_specs; (* filter out pre's which failed re-exe *)
    List.iter add_spec new_specs; (* add new specs *)
    SpecMap.iter convert !current_specs;  
    !res,!changed

let wnodes_todo = ref WeightedStringSet.empty

(* Return true if [node] is done and requires no further analysis *)
let node_is_done node =
  not (WeightedStringSet.mem (node,CallGraph.get_weight node) !wnodes_todo) 

(* Return true if [node] has just become done *)
let nodes_become_done node : string list =
  let recursive_dependents = CallGraph.get_recursive_dependents node in
  let nonrecursive_dependents = CallGraph.get_nonrecursive_dependents node in
    if
      get_timestamp node <> 0 &&
	get_status node == INACTIVE &&
	get_phase node == RE_EXECUTION &&
	StringSet.for_all node_is_done nonrecursive_dependents &&
	StringSet.for_all node_is_up_to_date recursive_dependents
    then
      let nodes_to_remove =
	(* the node itself if not recursive, otherwise all the recursive circle *)
	StringSet.add node recursive_dependents
      in StringSet.elements nodes_to_remove
    else []

(** Write log file for the proc *)
let proc_write_log pname =
  let pdesc = proc_name_to_proc_desc pname in
  let nodes = List.sort node_compare (proc_desc_get_nodes pdesc) in
  let linenum = (node_get_loc (List.hd nodes)).Cil.line in
  let fd,fmt = Html.create [pname]
  in
    F.fprintf fmt "<center><h1>Procedure %a</h1></center>@\n" (Html.pp_line_link ~text:(Some pname) []) linenum;
    List.iter (fun n -> Html.pp_node_link [] (get_node_description n) fmt (node_to_sid n)) nodes;
    pp_summary_html fmt (get_summary pname);
    Html.close (fd,fmt)

let post_process_nodes procs_done =
  List.iter (fun n ->
    wnodes_todo := WeightedStringSet.remove (n,CallGraph.get_weight n) !wnodes_todo;
    Stats.time "proc_write_log" proc_write_log n
  ) procs_done

let parallel_execution num_processes analyze_proc filter_out process_result : unit =
  parallel_mode := num_processes > 1 || !Config.max_num_proc > 0;
  wnodes_todo := compute_weighed_nodes ();
  let avail_num = ref num_processes (* number of processors available *)
  in

  let node_is_not_up_to_date node =
    not (node_is_up_to_date node)
  in

  (* Return true if [node] is not up to date and it can be analyzed
     right now *)
  let wnode_can_be_analyzed (node,weight) : bool =
    get_status node == INACTIVE &&
    (node_is_not_up_to_date node || get_timestamp node = 0) &&
    StringSet.for_all node_is_done (CallGraph.get_nonrecursive_dependents node)
  in

  let process_one_node node weight =
    (*
      E.stderr "@[<v 3>   *********** Summary of %s ***********@," node;
      E.stderr "%a@]@\n" pp_summary (get_summary node);
    *)
    if filter_out node
    then
      post_process_nodes [node]
    else
      (set_status node ACTIVE;
       update_dependency_map node;
       if !parallel_mode then
	 let p_str = Process.spawn_fun analyze_proc
	 in
	   Timing_log.event_start node;
	   Process.send_to_child p_str (Some (node,weight));
	   decr avail_num
       else
	 process_result node (analyze_proc (node,weight)))
  in

  let wait_for_next_result () =
    try
      let p_str,v = Process.receive_from_child () in
      let (node,weight) = Process.get_last_input p_str
      in
	(try process_result node v
	  with exn -> assert false);
	Timing_log.event_finish node;
	Process.kill_process p_str;
	incr avail_num
    with
      | Sys_blocked_io -> ()
  in

    while not (WeightedStringSet.is_empty !wnodes_todo) do
      if !avail_num > 0 then
	let analyzable_nodes = WeightedStringSet.filter wnode_can_be_analyzed !wnodes_todo in
(*
	  E.log "Nodes todo: %a@\n" pp_weightednodeset !wnodes_todo;
	  E.log "Analyzable nodes: %a@\n" pp_weightednodeset analyzable_nodes;
*)
	try
	  let node,weight = WeightedStringSet.max_elt analyzable_nodes
	  in process_one_node node weight
	with Not_found ->
	  if !avail_num < num_processes (* some other thread is doing work *)
	  then wait_for_next_result ()
	  else
	    (E.stderr "Error: can't analyze any procs. Printing current spec table@\n@[<v>%a@]@." pp_spec_table ();
	     raise (Failure "Stopping"))
      else
	wait_for_next_result ()
    done

(** [parallel_iter_nodes analyze_proc process_result filter_out]
    executes [analyze_proc] in parallel as much as possible as allowed
    by the call graph, and applies [process_result] to the result as
    soon as it is returned by a child process. If [filter_out] returns
    true, no execution. *)
let parallel_iter_nodes (analyze_proc : string -> 'a) (process_result : string->'a -> unit) (filter_out : string -> bool) : unit =
  let num_processes = if !Config.max_num_proc = 0 then !Config.num_cores else !Config.max_num_proc
  in
    print_call_graph_dotty ();
    Unix.handle_unix_error (parallel_execution num_processes (fun (n,w) -> analyze_proc n) filter_out) process_result
