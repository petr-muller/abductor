(*
 *
 * Copyright (c) 2006-2008,
 *  Cristiano Calcagno    <ccris@doc.ic.ac.uk>
 *  Dino Distefano        <ddino@dcs.qmul.ac.uk>
 *  Peter O'Hearn         <ohearn@dcs.qmul.ac.uk>
 *  Hongseok Yang         <hyang@dcs.qmul.ac.uk>
 * All rights reserved.
 *)

(** Translation from cil to sil *)

(** list of instructions to translate impure expressions, and the list
    of local variables generated *)
type temp_list = Ident.ident list * Sil.instr list

val trans_typ : Cil.typ -> Sil.typ
val trans_exp : Cil.fundec -> Cil.exp -> Cil.location -> temp_list * Sil.exp
val trans_lval : Cil.fundec -> Cil.lval -> Cil.location -> temp_list * Sil.exp
val trans_explist : Cil.fundec -> Cil.exp list -> Cil.location -> temp_list * Sil.exp list
val trans_typeinfo : Cil.typeinfo -> Sil.typ
val trans_compinfo : Cil.compinfo -> Sil.typ
val trans_typeinfo_decls : Cil.typeinfo list -> unit
val trans_compinfo_decls : Cil.compinfo list -> unit
val trans_instr : Cil.fundec -> Cil.instr -> temp_list

(** Return the set of function names whose address has been taken *)
val get_fun_address_set : unit -> Ident.NameSet.t
