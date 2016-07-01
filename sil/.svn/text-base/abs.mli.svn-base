(*
 *
 * Copyright (c) 2006-2008,
 *  Cristiano Calcagno    <ccris@doc.ic.ac.uk>
 *  Dino Distefano        <ddino@dcs.qmul.ac.uk>
 *  Peter O'Hearn         <ohearn@dcs.qmul.ac.uk>
 *  Hongseok Yang         <hyang@dcs.qmul.ac.uk>
 * All rights reserved.
 *)

(** Abstraction *)

open Propset

(** Create abstraction rules from the definition of a type *)
val create_absrules_from_tdecl : Sil.typename -> unit

(** Abstract a proposition. *)
val abstract : Prop.prop -> Prop.prop

(** Abstract each proposition in [propset] *)
val lifted_abstract : propset -> propset

val abs_rules_reset : unit -> unit
