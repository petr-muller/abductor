(*
 *
 * Copyright (c) 2006-2008,
 *  Cristiano Calcagno    <ccris@doc.ic.ac.uk>
 *  Dino Distefano        <ddino@dcs.qmul.ac.uk>
 *  Peter O'Hearn         <ohearn@dcs.qmul.ac.uk>
 *  Hongseok Yang         <hyang@dcs.qmul.ac.uk>
 * All rights reserved.
 *)

(** Functions for "Smart" Pattern Matching *)

open Ident
open Sil
open Prop

val hpara_match_with_impl : bool -> hpara -> hpara -> bool
val hpara_dll_match_with_impl : bool -> hpara_dll -> hpara_dll -> bool



(** Type for a hpred pattern. [flag=false] means that the implication 
   between hpreds is not considered, and [flag=true] means that it is 
   considered during pattern matching. *)
type hpred_pat = {hpred : hpred; flag : bool}

val pp_hpat : Format.formatter -> hpred_pat -> unit

val pp_hpat_list : Format.formatter -> hpred_pat list -> unit

type sidecondition = prop -> subst -> bool

(** [prop_match_with_impl p condition vars hpat hpats]
    returns [(subst,p_leftover)] such that 
    1) [dom(subst) = vars]
    2) [p |- (hpat.hpred * hpats.hpred)[subst] * p_leftover].
    Using the flag [field], we can control the strength of |-. *) 
val prop_match_with_impl : prop -> sidecondition -> ident list -> hpred_pat -> hpred_pat list -> (subst * prop) option


