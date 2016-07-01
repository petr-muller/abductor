(*
 *
 * Copyright (c) 2006-2008,
 *  Cristiano Calcagno    <ccris@doc.ic.ac.uk>
 *  Dino Distefano        <ddino@dcs.qmul.ac.uk>
 *  Peter O'Hearn         <ohearn@dcs.qmul.ac.uk>
 *  Hongseok Yang         <hyang@dcs.qmul.ac.uk>
 * All rights reserved.
 *)

(** Functions for Sets of Propositions with and without sharing *)

open Prop

(** {2 Sets of Propositions} *)

(** A set of propositions. *)
type propset

(** Compare propsets *)
val propset_compare : propset -> propset -> int

(** Singleton set. *)
val propset_singleton : prop -> propset

(** Set membership. *)
val propset_mem : prop -> propset -> bool

(** Set union. *)
val propset_union : propset -> propset -> propset

(** Set intersection *)
val propset_inter : propset -> propset -> propset

(** Add [prop] to [propset]. *)
val propset_add : prop -> propset -> propset

(** Set difference. *)
val propset_diff : propset -> propset -> propset

(** The empty set of propositions. *)
val propset_empty : propset

(** Set emptiness check. *)
val propset_is_empty : propset -> bool

(** Size of the set *)
val propset_size : propset -> int

val proplist2propset : prop list -> propset

val propset2proplist : propset -> prop list

(** Apply function to all the elements of [propset]. *)
val propset_map : (prop -> prop) -> propset -> propset

(** Apply function to all the elements of [propset], removing those where it returns [None]. *)
val propset_map_option : (prop -> prop option) -> propset -> propset

(** [propset_fold f pset a] computes [(f pN ... (f p2 (f p1 a))...)],
    where [p1 ... pN] are the elements of pset, in increasing
    order. *)
val propset_fold : ('a -> prop -> 'a) -> 'a -> propset -> 'a

(** [propset_iter f pset] computes (f p1;f p2;..;f pN)
    where [p1 ... pN] are the elements of pset, in increasing order. *)
val propset_iter : (prop -> unit) -> propset -> unit

val propset_subseteq : propset -> propset -> bool

(** Set emptiness check. *)
val propset_is_empty : propset -> bool

(** Size of the set *)
val propset_size : propset -> int

val propset_filter : (prop -> bool) -> propset -> propset

(** {2 Pretty print} *)

val pp_proplist : Format.formatter -> prop list -> unit

(** Pretty print a set of propositions. *)
val pp_propset : Format.formatter -> propset -> unit

(** dump a propset *)
val d_propset : propset -> unit

val pp_propset_dotty : Format.formatter -> propset -> unit 

val pp_propset_dotty_file : string -> propset -> unit

val pp_proplist_dotty_file : string -> prop list -> unit
