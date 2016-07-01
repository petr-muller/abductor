(*
 *
 * Copyright (c) 2006-2008,
 *  Cristiano Calcagno    <ccris@doc.ic.ac.uk>
 *  Dino Distefano        <ddino@dcs.qmul.ac.uk>
 *  Peter O'Hearn         <ohearn@dcs.qmul.ac.uk>
 *  Hongseok Yang         <hyang@dcs.qmul.ac.uk>
 * All rights reserved.
 *)

(** Interprocedural footprint analysis *)

(** Execute the function call and return the list of results with return value *)
val exe_function_call: string -> (Sil.exp * Sil.typ) list -> Prop.prop ->  Prop.prop list
