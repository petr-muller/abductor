(*
 *
 * Copyright (c) 2006-2008,
 *  Cristiano Calcagno    <ccris@doc.ic.ac.uk>
 *  Dino Distefano        <ddino@dcs.qmul.ac.uk>
 *  Peter O'Hearn         <ohearn@dcs.qmul.ac.uk>
 *  Hongseok Yang         <hyang@dcs.qmul.ac.uk>
 * All rights reserved.
 *)

(** Functions for Propositions (i.e., Symbolic Heaps) *)

open Ident
open Sil

(** Proposition. *)
type prop

exception Bad_footprint
exception Cannot_star

(** {2 Basic Functions for propositions} *)

(** Compare propositions *)
val prop_compare : prop -> prop -> int

(** Checks the equality of two propositions *)
val prop_equal : prop -> prop -> bool

(** Pretty print a substitution. *)
val pp_sub : Format.formatter -> subst -> unit

(** Dump a substitution. *)
val d_sub : subst -> unit

(** Pretty print a pi. *)
val pp_pi : Format.formatter -> Sil.atom list -> unit

(** Dump a pi. *)
val d_pi : Sil.atom list -> unit

(** Pretty print a sigma. *)
val pp_sigma : Format.formatter -> Sil.hpred list -> unit

(** Dump a sigma. *)
val d_sigma : Sil.hpred list -> unit

(** Pretty print a proposition. *)
val pp_prop : Format.formatter -> prop -> unit

(** Dump a proposition. *)
val d_prop : prop -> unit

(** Compute free non-program variables of pi *)
val pi_fav : atom list -> fav

val pi_fav_add : fav -> atom list -> unit

(** Compute free non-program variables of sigma *)
val sigma_fav_add : fav -> hpred list -> unit

val sigma_fav : hpred list -> fav

(** returns free non-program variables that are used to express
the contents of stack variables *)
val sigma_fav_in_pvars_add : fav -> hpred list -> unit

(** Compute free non-program variables of prop *)
val prop_fav_add : fav -> prop -> unit

val prop_fav: prop -> fav

val prop_live_fav: prop -> fav

(** Apply substitution for pi *)
val pi_sub : subst -> atom list -> atom list

(** Apply subsitution for sigma *)
val sigma_sub : subst -> hpred list -> hpred list

(** Apply subsitution to prop. Result is normalized. *)
val prop_sub : subst -> prop -> prop

(** Change exps in prop by [f] *)
val prop_expmap : (Sil.exp -> Sil.exp) -> prop -> prop

(** Apply renaming substitution to a proposition without normalizing. *)
val prop_apply_renaming_no_normalize : subst -> prop -> prop

(** Relaces all expressions in the [hpred list] using the first argument.
    Assume that the first parameter defines a partial function.
    No expressions inside hpara are replaced. *)
val sigma_replace_exp : (exp * exp) list -> hpred list -> hpred list


(** {2 Normalization} *)

(** Normalize [exp] using the pure part of [prop].  Later, we should
    change this such that the normalization exposes offsets of [exp]
    as much as possible. *)
val exp_normalize_prop : prop -> exp -> exp

val atom_normalize_prop : prop -> atom -> atom

val strexp_normalize_prop : prop -> strexp -> strexp

val hpred_normalize_prop : prop -> hpred -> hpred

val sigma_normalize_prop : prop -> hpred list -> hpred list

(** {2 Queries about propositions} *)

(** Check if the sigma part of the proposition is emp *)
val prop_is_emp : prop -> bool


(** {2 Functions for changing and generating propositions} *)

(** Construct a disequality. *)
val mk_neq :  exp -> exp -> atom

(** Construct a pointsto. *)
val mk_ptsto :  exp -> strexp -> exp -> hpred

(** Construct a points-to predicate for an expression using [name] as
    base for fresh identifiers. *)
val mk_ptsto_exp : name -> exp * exp * exp option -> hpred

(** Construct a points-to predicate for a single program variable. *)
val mk_ptsto_lvar : pvar * typ * exp option -> hpred 

(** Construct a lseg predicate *)
val mk_lseg : lseg_kind -> hpara -> exp -> exp -> exp list -> hpred

(** Construct a dllseg predicate *)
val mk_dllseg : lseg_kind -> hpara_dll -> exp -> exp -> exp -> exp -> exp list -> hpred

(** Construct a hpara *)
val mk_hpara : ident -> ident -> ident list -> ident list -> hpred list -> hpara

(** Construct a dll_hpara *)
val mk_dll_hpara : ident -> ident -> ident -> ident list -> ident list -> hpred list -> hpara_dll

(** Proposition [true /\ emp]. *)
val prop_emp : prop

(** Conjoin a heap predicate by separating conjunction. *)
val prop_hpred_star : prop -> hpred -> prop

(** Conjoin a list of heap predicates by separating conjunction *)
val prop_sigma_star : prop -> hpred list -> prop

(** Implementation of [*] for the field-splitting model *)
val sigma_star_fld : hpred list -> hpred list -> hpred list

(** Conjoin a pure atomic predicate by normal conjunction. *)
val prop_atom_and : ?footprint:bool -> prop -> atom -> prop

(** Conjoin [exp1]=[exp2] with a symbolic heap [prop]. *)
val conjoin_eq :  ?footprint:bool -> exp -> exp -> prop -> prop

(** Conjoin [exp1]!=[exp2] with a symbolic heap [prop]. *)
val conjoin_neq :  ?footprint:bool -> exp -> exp -> prop -> prop

(** Return the equalities in the proposition *)
val prop_get_equalities : prop -> (exp * exp) list

(** Return the sub part of [prop]. *)
val prop_get_sub : prop -> subst

(** Replace the sub part of [prop]. *)
val prop_replace_sub : subst -> prop -> prop

(** Return the pi part of [prop]. *)
val prop_get_pi : prop -> atom list

(** Return the pure part of [prop]. *)
val prop_get_pure : prop -> atom list

(** Replace the pi part of [prop]. *)
val prop_replace_pi : atom list -> prop -> prop

(** Remove equalities of the form fp=exp for footprint vars fp. *)
val prop_abs_pi_footprint_vars : prop -> prop

(** Return the sigma part of [prop] *)
val prop_get_sigma : prop -> hpred list

(** Replace the sigma part of [prop] *)
val prop_replace_sigma : hpred list -> prop -> prop

(** Generate [prop] from [hpred list] *)
val prop_of_sigma : hpred list -> prop

(** Create a [prop] without any normalization *)
val prop_create_verbatim : atom list -> hpred list -> prop

(** Allocate a global variable *)
val prop_init_global :  pvar -> typ -> prop -> prop

(** Initialize proposition for execution given formal and global
    parameters. The footprint is initialized according to the
    execution mode. *)
val prop_init_formals_locals_seed :  (pvar * typ * exp option) list -> (pvar * typ * exp option) list -> prop -> prop

(** Remove seed vars from a prop *)
val prop_remove_seed_vars : prop -> prop

(** Deallocate the stack variables in list_var, and replace them by normal variables. *)
val prop_dispose_stack_proc : prop -> pvar list -> prop

(** Canonicalize the names of primed variables. *)
val prop_rename_primed_footprint_vars : prop -> prop

(** [prop_copy_footprint_pure p1 p2] copies the footprint and pure part of [p1] into [p2] *)
val prop_copy_footprint_pure : prop -> prop -> prop

(** Extract the footprint and return it as a prop *)
val prop_extract_footprint : prop -> prop

(** Extract the footprint, add a local stack and return it as a prop *)
val prop_extract_footprint_for_abs : prop -> prop * pvar list

(** Extract the (footprint,current) pair *)
val prop_extract_spec : prop -> (prop*prop)

(** [prop_set_fooprint p p_foot] sets proposition [p_foot] as footprint of [p]. *)
val prop_set_footprint : prop -> prop -> prop

(** Strengthen the footprint by adding pure facts from the current part *)
val prop_strengthen_footprint : prop -> prop

(** [prop_footprint_add_pi_sigma_starfld_sigma prop pi sigma missing_fld] extends the footprint of [prop] with [pi,sigma] and extends the fielsd of |-> with [missing_fld] *)
val prop_footprint_add_pi_sigma_starfld_sigma : prop -> (atom list) -> (hpred list) -> (hpred list) -> prop option

(** [prop_set_fooprint p p_foot] removes a local stack from [p_foot],
    and sets proposition [p_foot] as footprint of [p]. *)
val prop_set_footprint_for_abs : prop -> prop -> pvar list -> prop

(** {2 Functions for existentially quantifying and unquantifying variables} *)

(** Existentially quantify the [ids] in [prop]. *)
val exist_quantify : fav -> prop -> prop

(** convert the footprint vars to primed vars. *)
val prop_normal_vars_to_primed_vars : prop -> prop

(** convert the primed vars to normal vars. *)
val prop_primed_vars_to_normal_vars : prop -> prop

(** Rename all primed variables. *)
val prop_rename_primed_fresh : prop -> prop

(** {2 Prop iterators} *)

(** Iterator over the sigma part. Each iterator has a current [hpred]. *)
type 'a prop_iter

(** Create an iterator, return None if sigma part is empty. *)
val prop_iter_create : prop -> ('a prop_iter) option

(** Return the prop associated to the iterator. *)
val prop_iter_to_prop : 'a prop_iter -> prop

(** Remove the current element from the iterator, and return the prop
    associated to the resulting iterator. *)
val prop_iter_remove_curr_then_to_prop : 'a prop_iter -> prop

(** Return the current hpred and state. *)
val prop_iter_current : 'a prop_iter -> (hpred * 'a option)

(** Return the next iterator. *)
val prop_iter_next : 'a prop_iter -> 'a prop_iter option

(** Remove the current hpred and return the next iterator. *)
val prop_iter_remove_curr_then_next : 'a prop_iter -> 'a prop_iter option

(** Update the current element of the iterator. *)
val prop_iter_update_current : 'a prop_iter -> hpred -> 'a prop_iter

(** Scan sigma to find an [hpred] satisfying the filter function. *)
val prop_iter_find : 'a prop_iter -> (hpred -> 'a option) -> 'a prop_iter option

(** Update the current element of the iterator by a nonempty list of
    elements. *)
val prop_iter_update_current_by_list : 'a prop_iter -> hpred list -> 'a prop_iter

(** Add a pointsto for [lexp:typ] to the iterator and to the
    footprint, if it's compatible with the allowed footprint
    variables. *)
val prop_iter_add_hpred_footprint : 'a prop_iter -> exp*typ -> 'a prop_iter

(** Add a pointsto for [lexp:typ] to the sigma and footprint of a prop,
    if it's compatible with the allowed footprint variables. Then,
    change it into a iterator. *)
val prop_iter_add_hpred_footprint_to_prop : prop -> exp*typ -> 'a prop_iter

(** Set the state of an iterator *)
val prop_iter_set_state : 'a prop_iter -> 'b -> 'b prop_iter

(** Rename [ident] in [iter] by a fresh primed identifier *)
val prop_iter_make_id_primed : Ident.ident -> 'a prop_iter -> 'a prop_iter

(** Collect garbage fields. *)
val prop_iter_gc_fields :  'a prop_iter -> 'a prop_iter

(** Expand PE listsegs if the flag is on. *)
val prop_expand : prop -> prop list

module Metrics : sig
(** Compute a size value for the prop, which indicates its complexity *)
val prop_size : prop -> int

(** Approximate the size of the longest chain by counting the max
    number of |-> with the same type and whose lhs is primed or
    footprint *)
val prop_chain_size : prop -> int
end

(** [prop_iter_extend_ptsto iter lexp] extends the current psto
    predicate in [iter] with enough fields to follow the path in
    [lexp] -- field splitting model *)
val prop_iter_extend_ptsto : 'a prop_iter -> exp -> 'a prop_iter

(** Check if the path in exp exists already in the current ptsto predicate *)
val prop_iter_check_fields_ptsto : 'a prop_iter -> exp -> bool

(** Extend all the structs in [prop] with fresh variables *)
val prop_extend_all_structs : Ident.kind -> prop -> prop

(** Add the occurring names to the set *)
val prop_names_add : NameSet.t -> prop -> unit

(** Update the names in the prop *)
val prop_names_update : NameEnv.t -> prop -> prop
