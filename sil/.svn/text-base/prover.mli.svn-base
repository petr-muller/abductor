(*
 *
 * Copyright (c) 2006-2008,
 *  Cristiano Calcagno    <ccris@doc.ic.ac.uk>
 *  Dino Distefano        <ddino@dcs.qmul.ac.uk>
 *  Peter O'Hearn         <ohearn@dcs.qmul.ac.uk>
 *  Hongseok Yang         <hyang@dcs.qmul.ac.uk>
 * All rights reserved.
 *)

(** Functions for Theorem Proving *)

open Ident
open Sil
open Prop

(** Check [prop |- exp1=exp2]. *)
val check_equal : prop -> exp -> exp -> bool

(** Check whether [prop |- exp1!=exp2]. *)
val check_disequal : prop -> exp -> exp -> bool

(** Inconsistency checking ignoring footprint. *)
val check_inconsistency_base : prop -> bool

(** Inconsistency checking. *)
val check_inconsistency : prop -> bool
  
(** Check whether [prop |- allocated(exp)]. *)
val check_allocatedness : prop -> exp -> bool

(** [check_implication p1 p2] returns true if [p1|-p2] *)
val check_implication : prop -> prop -> bool

(** [check_implication_for_footprint p1 p2] returns
    [Some(sub,frame,missing)] if [sub(p1 * missing) |- sub(p2 *
    frame)] where [sub] is a substitution which instantiates the
    primed vars of [p1] and [p2], which are assumed to be disjoint. *)
val check_implication_for_footprint : prop -> prop -> (subst * subst * hpred list * (atom list) * (hpred list) * (hpred list) * (hpred list)) option

(** [is_root prop base_exp exp] checks whether [base_exp =
    exp.offlist] for some list of offsets [offlist]. If so, it returns
    [Some(offlist)].  Otherwise, it returns [None]. Assumes that
    [base_exp] points to the beginning of a structure, not the middle. *)
val is_root : prop -> exp -> exp -> offset list option

(** Find miminum set of pi's  in [cases] whose disjunction covers true *)
val find_minimum_pure_cover : (Sil.atom list * 'a) list -> (Sil.atom list * 'a) list option
