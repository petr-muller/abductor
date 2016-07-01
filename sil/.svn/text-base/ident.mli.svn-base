(*
 *
 * Copyright (c) 2006-2008,
 *  Cristiano Calcagno    <ccris@doc.ic.ac.uk>
 *  Dino Distefano        <ddino@dcs.qmul.ac.uk>
 *  Peter O'Hearn         <ohearn@dcs.qmul.ac.uk>
 *  Hongseok Yang         <hyang@dcs.qmul.ac.uk>
 * All rights reserved.
 *)

(** Identifiers: program variables and logical variables *)

(** Program and logical variables. *)
type ident

(** Names used to replace strings. *)
type name

(** Kind of identifiers. *)
type kind

(** Environments for names: keep relation between names and strings -- to be used for serialization *)
module NameEnv :
sig
  (** Environment mapping names to string *)
  type t 

  (** [name_update env name] updates [name], which was defined using
      [env], to use (and possibly extend) the current environment *)
  val name_update : t -> name -> name
  val ident_update : t -> ident -> ident
end

module NameSet :
sig
  type t
  val create : unit -> t
  val add : t -> name -> unit
  val add_string : t -> string -> unit
  val add_ident : t -> ident -> unit
  val to_env : t -> NameEnv.t
  val pp : Format.formatter -> t -> unit
end

val kprimed : kind
val knormal : kind
val kfootprint : kind

(** hash table for a type environment *)
module NameHash : Hashtbl.S with type key = name

(** Name used for tmp variables *)
val name_siltmp : name 

(** Convert a string to a name. *)
val string_to_name : string -> name

(** Convert a name to a string. *)
val name_to_string : name -> string

(** Name of the identifier. *)
val ident_name : ident -> name

(** Kind of the identifier. *)
val ident_kind : ident -> kind

val create_ident : kind -> name -> int -> ident

(** Generate a normal identifier with the given name and stamp. *)
val create_normal_ident : name -> int -> ident

(** Generate a primed identifier with the given name and stamp. *)
val create_primed_ident : name -> int -> ident

(** Generate a footprint identifier with the given name and stamp. *)
val create_footprint_ident : name -> int -> ident

(** Create a fresh normal identifier with the given name. *)
val create_fresh_normal_ident : name -> ident

(** Create a fresh footprint identifier with the given name. *)
val create_fresh_footprint_ident : name -> ident

(** Create a fresh primed identifier with the given name. *)
val create_fresh_primed_ident : name -> ident

(** Check whether an identifier is primed or not. *)
val ident_is_primed : ident -> bool

(** Check whether an identifier is normal or not. *)
val ident_is_normal : ident -> bool

(** Check whether an identifier is footprint or not. *)
val ident_is_footprint : ident -> bool

(** Check whether an identifier is a footprint variable or not.*)
val ident_is_footprint : ident -> bool

(** Convert a primed ident into a nonprimed one, keeping the stamp. *)
val make_ident_unprimed : ident -> ident

(** Get the stamp of the identifier *)
val ident_get_stamp: ident -> int

(** Set the stamp of the identifier *)
val ident_set_stamp: ident -> int -> ident

(** {2 Comparision Functions} *)

(** Equality police: only defined on integers. *)
val (=) : int -> int -> bool

(** Disquality police: only defined on integers. *)
val (<>) : int -> int -> bool

(** Compare police: generic compare disabled. *)
val compare : unit

(** Efficient comparison for integers *)
val int_compare : int -> int -> int

(** Comparison for names. *)
val name_compare : name -> name -> int

(** Equality for names. *)
val name_equal : name -> name -> bool

(** Equality for kind. *)
val kind_equal : kind -> kind -> bool

(** Comparison for identifiers. *)
val ident_compare : ident -> ident -> int

(** Equality for identifiers. *)
val ident_equal : ident -> ident -> bool

(** Comparison for lists of identities *)
val ident_list_compare : ident list -> ident list -> int

(** Equality for lists of identities *)
val ident_list_equal : ident list -> ident list -> bool

(** {2 Pretty Printing} *)

(** Pretty print a name. *)
val pp_name : Format.formatter -> name -> unit

(** Pretty print an identifier. *)
val pp_ident : Format.formatter -> ident -> unit

(** Pretty print a list of identifiers. *)
val pp_ident_list : Format.formatter -> ident list -> unit

(** Pretty print a list of names. *)
val pp_name_list : Format.formatter -> name list -> unit
