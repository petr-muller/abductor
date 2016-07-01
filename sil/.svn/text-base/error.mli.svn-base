(*
 *
 * Copyright (c) 2006-2008,
 *  Cristiano Calcagno    <ccris@doc.ic.ac.uk>
 *  Dino Distefano        <ddino@dcs.qmul.ac.uk>
 *  Peter O'Hearn         <ohearn@dcs.qmul.ac.uk>
 *  Hongseok Yang         <hyang@dcs.qmul.ac.uk>
 * All rights reserved.
 *)

(** Functions for printing at different levels of verbosity *)

type colour

val black : colour
val red : colour
val green : colour
val yellow : colour
val blue : colour
val magenta : colour
val cyan : colour

(** Return the next "coloured" (i.e. not black) colour *)
val next_colour : unit -> colour

(** Print escape code to change the terminal's colour *)
val change_terminal_colour : colour -> unit

(** type of printable elements *)
type print_type =
    | PTstr
    | PTstrln
    | PTpvar
    | PTloc
    | PToff
    | PToff_list
    | PTtyp_full
    | PTtexp_full
    | PTexp
    | PTexp_list
    | PTatom
    | PTsexp
    | PThpred
    | PTtyp_list
    | PTsub
    | PTpi
    | PTsigma
    | PTprop
    | PTpropset
    | PTjprop_short
    | PTjprop_list
    | PTinstr
    | PTinstr_list
    | PTnode_instrs
    | PTpathset

(** delayable print action *)
type print_action =
    print_type * Obj.t (** data to be printed *)

(** extend he current print log *)
val add_print_action : print_action -> unit

(** hook for a printer for delayed print actions
    implemented and assigned later when all the data structures are visible *)
val force_delayed_print_ref : (Format.formatter -> print_action -> unit) ref

(** Printing mode: DEFAULT prints unless test mode is false and function is log; ALWAYS prints all the time; NEVER prints never *)
type mode = DEFAULT | ALWAYS | NEVER

(** Functor to build custom printer *)
module MyErr :
  functor (Elt : sig val mode : mode end) ->
    sig
      (** Set the colours of this custom printer *)
      val set_colour : colour -> unit

      (** Set the mode of this custom printer *) 
      val set_mode : mode -> unit

      (** In DEFAULT mode, print if test mode is false *)
      val log : ('a, Format.formatter, unit) format -> 'a

      (** dump a string *)
      val d_str : string -> unit
      (** dump a string plus newline *)
      val d_strln : string -> unit
      (** dump a newline *)
      val d_ln : unit -> unit
      (** dump an indentation *)
      val d_indent : int -> unit

      (** In DEFAULT mode, always print *)
      val err : ('a, Format.formatter, unit) format -> 'a

      (** In DEFAULT mode, always print on stderr *)
      val stderr : ('a, Format.formatter, unit) format -> 'a
    end

module DB : sig
  val init : unit -> unit (** Initialize the datbase file *)
  type path = string list
  val relative_path : path -> string
  val absolute_path : path -> string
end

module Html : sig
  val create : ?with_background:bool -> DB.path -> Unix.file_descr * Format.formatter
  val open_out : DB.path -> Unix.file_descr * Format.formatter
  val close : Unix.file_descr * Format.formatter -> unit
  val pp_hline : Format.formatter -> unit -> unit (** Print a horizontal line *)
  val pp_start_listing : Format.formatter -> unit -> unit (** Print start listing *)
  val pp_end_listing : Format.formatter -> unit -> unit (** Print end listing *)
  val pp_node_link :  DB.path -> string -> Format.formatter -> int -> unit (** Print an html link to the given node *)
  val pp_proc_link : DB.path -> string -> Format.formatter -> string -> unit (** Print an html link to the given proc *)
  val pp_line_link : ?with_name:bool -> ?text:(string option) -> DB.path -> Format.formatter -> int -> unit (** Print an html link to the given line number of the current source file *)
  val pp_session_link :  ?with_name:bool -> string list -> Format.formatter -> int * int * int -> unit (** Print an html link given node id and session *)
end

(** Create a new node and return [true], or prepare to append to existing node and return [false] *)
val start_node : int -> Cil.location -> string -> int list -> int list -> bool
val finish_node : int -> unit

val reset_delayed_prints : unit -> unit
val force_delayed_prints : unit -> unit
