(*
 *
 * Copyright (c) 2006-2008,
 *  Cristiano Calcagno    <ccris@doc.ic.ac.uk>
 *  Dino Distefano        <ddino@dcs.qmul.ac.uk>
 *  Peter O'Hearn         <ohearn@dcs.qmul.ac.uk>
 *  Hongseok Yang         <hyang@dcs.qmul.ac.uk>
 * All rights reserved.
 *)

(**  Control Flow Graph for Interprocedural Analysis *)

(** {2 ADT node and proc_desc} *)

type node

type proc_desc

type nodekind = 
  | Start_node of proc_desc
  | Exit_node of proc_desc 
  | Stmt_node of Sil.instr list | Join_node 
  | Prune_node of Sil.instr list * Sil.exp
  | Call_node of proc_desc * Sil.instr list * (Sil.exp*Sil.typ) list
  | Return_Site_node of Sil.instr list
  | Skip_node of string

module StringSet : Set.S with type elt=string

module CallGraph : sig
  val reset : unit -> unit
  val add_edge : string -> string -> unit
  val add_node : string -> unit
  val get_weight : string -> int
  val get_dependents: string -> StringSet.t
  val get_nonrecursive_dependents: string -> StringSet.t
  val get_recursive_dependents: string -> StringSet.t
  val get_nodes_and_dependents : unit -> (string * StringSet.t) list
  val node_defined : string -> bool
  val delete_node : string -> (string*int) list
  val get_weighted_nodes : unit -> (string*int) list
  val pp_graph_dotty : Format.formatter -> unit
end

val dummy_node : node

val node_to_sid : node -> int

val node_get_succs : node -> node list

val node_get_preds : node -> node list

val node_get_kind : node -> nodekind

val node_set_kind : node -> nodekind -> unit

val node_get_loc : node -> Cil.location

val node_get_proc_desc : node -> proc_desc

val node_get_sil: node -> Sil.instr list 

val node_get_dead: node -> Ident.ident list 

val node_set_dead: node -> Ident.ident list -> unit

val node_get_dead_pvar: node -> Sil.pvar list 

val node_set_dead_pvar: node -> Sil.pvar list -> unit

val node_equal : node -> node -> bool

val node_compare : node -> node -> int

val pp_node : Format.formatter -> node -> unit

(** Print extended instructions for the node *)
val pp_node_instr : sub_instrs:bool -> Format.formatter -> node -> unit

(** Dump extended instructions for the node *)
val d_node_instrs : sub_instrs:bool -> node -> unit

(** Return a description of the cfg node *)
val get_node_description : node -> string

val pp_node_list : Format.formatter -> node list -> unit

val proc_desc_iter : (string -> proc_desc -> unit) -> unit

val proc_name_to_proc_desc : string -> proc_desc

val proc_desc_to_proc_name : proc_desc -> string

val proc_desc_get_globals : proc_desc -> Sil.pvar list

val proc_desc_set_globals : proc_desc -> Sil.pvar list -> unit

val proc_desc_get_fundec : proc_desc -> Cil.fundec

val proc_desc_get_formals : proc_desc -> Cil.varinfo list

val proc_desc_get_locals : proc_desc -> Cil.varinfo list

val proc_desc_get_start_node : proc_desc -> node

val proc_desc_get_exit_node : proc_desc -> node

val proc_desc_get_cil_ret_type : proc_desc -> Cil.typ

val proc_desc_get_cil_ret_var : proc_desc -> Sil.pvar

val proc_desc_get_nodes : proc_desc -> node list

(** {2 Functions for manipulating an interprocedural CFG} *)

val compute_icfg : Cil.file -> unit

(** Print the cfg with extra edges *)
val print_icfg_dotty : ((node*node) list) -> unit

val get_all_nodes : unit -> node list

(** Get all the fun declarations *)
val get_all_fundecs : unit -> Cil.fundec list

(** Get all the fun declarations *)
val get_ordered_fundec_list : unit -> Cil.fundec list


(** Add reserved function names which we handle in symbolic execution *)
val add_reserved_functions : string list -> unit
