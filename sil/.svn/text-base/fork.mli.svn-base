(*
 *
 * Copyright (c) 2006-2008,
 *  Cristiano Calcagno    <ccris@doc.ic.ac.uk>
 *  Dino Distefano        <ddino@dcs.qmul.ac.uk>
 *  Peter O'Hearn         <ohearn@dcs.qmul.ac.uk>
 *  Hongseok Yang         <hyang@dcs.qmul.ac.uk>
 * All rights reserved.
 *)

(** Implementation of the Parallel Interprocedural Footprint Analysis Algorithm *)

(** {2 Spec Tables} *)

type spec = {pre:Dom.joined_prop; post: Prop.prop list}

(** Spec where the names of variables are normalized *)
type norm_spec

type stats =
    {stats_time: float option; exn_log: Exceptions.exn_log}

type status = ACTIVE | INACTIVE

type phase = FOOTPRINT | RE_EXECUTION

type dependency_map_t

type summary =
    {sessions:int ref; (** Session number: how many nodes went trough symbolic execution *)
     timestamp:int; (** Timestamp of the specs, >= 0, increased every time the specs change *)
     status:status; (** ACTIVE when the proc is being analyzed *)
     phase:phase; (** in FOOTPRINT phase or in RE_EXECUTION PHASE *)
     dependency_map:dependency_map_t;  (** maps dependent procs to timestamp as last seen at the start of an analysys phase for this proc *)
     specs:norm_spec list;  (** list of specs *)
     stats:stats;  (** statistics: execution time and list of exceptions *)
    }

(** Return true if the proc is in the spec table *)
val proc_exists : string -> bool

(** Return the summary for the proc in the spec table *)
val get_summary : string -> summary

(** Set the summary for the proc in the spec table *)
val set_summary : string -> summary -> unit

(** Return the specs for the proc in the spec table *)
val get_specs : string -> spec list

(** Return the current phase for the proc *)
val get_phase : string -> phase

(** Return the current timestamp for the proc's specs *)
val get_timestamp : string -> int

(** Set the current status for the proc *)
val set_status : string -> status -> unit

(** [init_summary proc_name depend_list] initializes the summary for
    [proc_name] given dependent procs in list [depend_list]. Do nothing
    if a summary exists already *)
val init_summary : string  * string list -> unit

val summary_names_add : Ident.NameSet.t -> summary -> unit

(** Take saved summary and name environment, and update names using the current environment *)
val summary_names_update : Ident.NameEnv.t -> string -> summary -> summary

(** Iterate [f] on all the procs in the spec table *)
val proc_iter : (string -> summary -> unit) -> unit

(** Convert spec into normal form w.r.t. variable renaming *)
val spec_normalize : spec -> norm_spec

(** Print the summary *)
val pp_summary : Format.formatter -> summary -> unit

(** Print the spec *)
val pp_spec : Format.formatter -> spec -> unit

(** Print the specs *)
val pp_specs : Format.formatter -> spec list -> unit

(** {2 Algorithm} *)

val nodes_become_done :  string -> string list

val post_process_nodes : string list -> unit

(** Return the list of procedures which should perform a phase
    transition from [FOOTPRINT] to [RE_EXECUTION] *)
val should_perform_transition : string -> string list

(** Perform the transition from [FOOTPRINT] to [RE_EXECUTION] in spec table *)
val transition_footprint_re_exe : string -> Dom.joined_prop list -> unit

(** Update the specs of the current proc after the execution of one phase *)
val update_specs : string -> norm_spec list -> norm_spec list * bool

(** [parallel_iter_nodes analyze_proc process_result filter_out]
    executes [analyze_proc] in parallel as much as possible as allowed
    by the call graph, and applies [process_result] to the result as
    soon as it is returned by a child process. If [filter_out] returns
    true, no execution. *)
val parallel_iter_nodes : (string->'a) -> (string->'a->unit) -> (string->bool) -> unit

(** print the timing info for the processes *)
val print_timing : unit -> unit

(** Print the stats for the given list of procedure names and given
    visited and total nodes *)
val print_stats : string list -> float -> Cfg_new.node list -> Cfg_new.node list -> unit

(** Write log file for the proc *)
val proc_write_log : string -> unit
