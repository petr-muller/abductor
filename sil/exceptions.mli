(*
 *
 * Copyright (c) 2006-2008,
 *  Cristiano Calcagno    <ccris@doc.ic.ac.uk>
 *  Dino Distefano        <ddino@dcs.qmul.ac.uk>
 *  Peter O'Hearn         <ohearn@dcs.qmul.ac.uk>
 *  Hongseok Yang         <hyang@dcs.qmul.ac.uk>
 * All rights reserved.
 *)

(** Functions for logging and printing exceptions *)

exception No_specs
exception Unknown_proc
exception Meet_required
exception Function_undefined
exception Wrong_argument_number
exception Abduction_Case_Not_implemented
exception Leak of Prop.prop * Prop.prop * Sil.hpred
exception Possible_memory_fault of Prop.prop
exception Memory_fault_Inconsistent_CallingState_MissingFP of Prop.prop
exception Array_of_pointsto
exception Re_exe_funcall
exception Symexec_memory_error
exception Filter_out

(** Turn an exception into a descriptive string *)
val recognize_exception : exn -> string

(** Return true if the exception is not serious and should be handled in timeout mode *)
val handle_exception : exn -> bool

(** Type of the exception log *)
type exn_log

(** Reset the exception log; to be called once per function *)
val reset_exn_log : unit -> unit

(** Empty exception log *)
val exn_log_empty : unit -> exn_log

(** Apply f to nodes and exception names *)
val exn_log_iter : (int -> bool -> string -> unit) -> exn_log -> unit

(** Add exception to the exception log *)
val log_exception : Cil.location -> int -> int -> exn -> unit

(** Update an old exn log with a new one *)
val exn_log_update : exn_log -> exn_log -> unit

(** Update the parameter exn log with the current exn log *)
val exn_log_update_with_current : exn_log -> unit

(** Print an exception log *)
val pp_exn_log : Format.formatter -> exn_log -> unit

(** Print an exception log in html format *)
val pp_exn_log_html : Error.DB.path -> Format.formatter -> exn_log -> unit

(** Print an exception log and add it to the global per-file table *)
val pp_exn_log_and_extend_table : Format.formatter -> exn_log -> unit

(** Size of the global per-file exception table for the footprint phase *)
val exn_table_size_footprint : unit -> int

(** Print stats for the global per-file exception table *)
val pp_exn_table_stats : Format.formatter -> unit -> unit

(** Print details of the global per-file exception table *)
val print_exn_table_details : Format.formatter -> unit
