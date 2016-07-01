(*
 *
 * Copyright (c) 2006-2008,
 *  Cristiano Calcagno    <ccris@doc.ic.ac.uk>
 *  Dino Distefano        <ddino@dcs.qmul.ac.uk>
 *  Peter O'Hearn         <ohearn@dcs.qmul.ac.uk>
 *  Hongseok Yang         <hyang@dcs.qmul.ac.uk>
 * All rights reserved.
 *)

(** Symbolic Execution *)

open Propset

(** [ptsto_lookup (lexp,strexp,typ) offlist id] given
    [lexp|->strexp:typ] returns the expression at position [offlist]
    in [strexp], together with [strexp], if the location [offlist]
    exists in [strexp]. If the location does not exist, it constructs
    [strexp'] containing [id] at [offlist], and returns
    ([ident],[strexp']).*)
val ptsto_lookup : (Sil.exp * Sil.strexp * Sil.typ) -> (Sil.offset list) -> Ident.ident -> (Sil.exp * Sil.strexp)

(** [ptsto_update (lexp,strexp,typ) offlist exp] given
    [lexp|->strexp:typ] returns an updated [strexp] obtained by
    replacing the expression at [offlist] with [exp]. *)
val ptsto_update : (Sil.exp * Sil.strexp * Sil.typ) -> (Sil.offset list) -> Sil.exp -> Sil.strexp

(** [rearrange lexp prop] rearranges [prop] into the form [prop' *
    lexp|->strexp:typ]. It returns an iterator with
    [lexp|->strexp:typ] as current predicate and the path (an [offset
    list]) which leads to [lexp] as the iterator state. *)
val rearrange : Sil.exp -> Sil.typ -> Prop.prop -> (Sil.offset list) Prop.prop_iter list

(** Prune a set of propositions based on [exp=1] *)
val prune : Sil.exp -> propset -> propset

(** Existentially quantify all identifiers in [ident list] for all
    propositions in [propset] *)
val lifted_exist_quantify : Sil.fav -> propset -> propset

(** symbolic execution on the level of sets of propositions *)
val lifted_sym_exec : propset -> Sil.instr -> propset
