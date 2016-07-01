(*
 *
 * Copyright (c) 2006-2008,
 *  Cristiano Calcagno    <ccris@doc.ic.ac.uk>
 *  Dino Distefano        <ddino@dcs.qmul.ac.uk>
 *  Peter O'Hearn         <ohearn@dcs.qmul.ac.uk>
 *  Hongseok Yang         <hyang@dcs.qmul.ac.uk>
 * All rights reserved.
 *)

(** {2 Functions for Implementing Locality} *)

(** Returns the set of auxiliary variables to store the initial values
    of parameters. These auxiliary variables implement cutpoints. *)
val aux_vars_get_param : Cil.fundec -> (Ident.ident * Ident.ident) list

(** Returns an auxiliary variable reserved for temporarily storing the
    return value of a procedure [proc_desc]. *)
val aux_vars_get_ret : Cil.fundec -> Ident.ident

(** Splits a proposition [prop1] into the unreachable part from [exp list] 
    and the reachable part. *)
val split : 
  Cil.fundec -> Sil.pvar list -> Sil.exp list -> Prop.prop 
  -> (Ident.ident * Ident.ident * Sil.exp) list * Prop.prop * Prop.prop

val combine : Cil.fundec -> Prop.prop -> Prop.prop -> Prop.prop option
