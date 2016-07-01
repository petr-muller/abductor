(*
 *
 * Copyright (c) 2006-2008,
 *  Cristiano Calcagno    <ccris@doc.ic.ac.uk>
 *  Dino Distefano        <ddino@dcs.qmul.ac.uk>
 *  Peter O'Hearn         <ohearn@dcs.qmul.ac.uk>
 *  Hongseok Yang         <hyang@dcs.qmul.ac.uk>
 * All rights reserved.
 *)

(** Pretty print a proposition in dotty format. *)

type kind_of_dotty_prop = Generic_proposition | Spec_precondition | Spec_postcondition | Lambda_pred of int * int

val pp_dotty : Format.formatter -> kind_of_dotty_prop -> Prop.prop -> unit

val pp_dotty_one_spec: Format.formatter -> Prop.prop -> Prop.prop list -> unit

val pp_dotty_prop_list: Format.formatter -> Prop.prop list -> int -> int -> unit

val reset_proposition_counter : unit -> unit

val reset_dotty_spec_counter : unit -> unit

