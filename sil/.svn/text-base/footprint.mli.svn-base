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

(** Perform one phase of the analysis for a procedure *)
val perform_analysis_phase : Cil.fundec -> Fork.spec list

(** Analyze [proc_name] and return the updated summary. Use module
    {!Timeout} to call {!perform_analysis_phase} with a time limit, and
    then return the updated summary. Executed as a child process. *)
val analyze_proc : string -> Fork.summary * Ident.NameEnv.t 

(** Process the result of the analysis of [proc_name]: update the
    returned summary and add it to the spec table. Executed in the
    parent process as soon as a child process returns a result. *)
val process_result : string -> Fork.summary * Ident.NameEnv.t -> unit

(** Return true if the analysis of [proc_name] should be
    skipped. Called by the parent process before attempting to analyze a
    proc. *)
val filter_out : string -> bool

(** Do footprint analysis *)
val doit : Cil.file -> unit

(** Feature description for footprint analysis *)
val feature : Cil.featureDescr
