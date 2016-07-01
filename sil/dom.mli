(** Join and Meet Operators *)

(** {2 Join Operators} *)

val prop_partial_join : Prop.prop -> Prop.prop -> Prop.prop option 

val propset_join : Propset.propset -> Propset.propset -> Propset.propset * Propset.propset

val join_time : float ref

(** Remember when a prop is obtained as the join of two other props *)
type joined_prop =
    | Prop of Prop.prop
    | Joined of Prop.prop * joined_prop * joined_prop

(** Print the toplevel prop *)
val pp_jprop_short : Format.formatter -> joined_prop -> unit

(** Dump the toplevel prop *)
val d_jprop_short : joined_prop -> unit

(** Number the props in the list and print the join info using the numbering *)
val pp_jprop_list : Format.formatter -> joined_prop list -> unit

(** dump a joined prop list *)
val d_jprop_list : joined_prop list -> unit

val jprop_to_prop : joined_prop -> Prop.prop

(** Comparison for joined_prop *)
val jprop_compare : joined_prop -> joined_prop -> int

(** Return true if the two join_prop's are equal *)
val jprop_equal : joined_prop -> joined_prop -> bool

val jprop_sub : Sil.subst -> joined_prop -> joined_prop

val jprop_fav_add : Sil.fav -> joined_prop -> unit

val jprop_apply_renaming_no_normalize : Sil.subst -> joined_prop -> joined_prop

val jprop_names_add : Ident.NameSet.t -> joined_prop -> unit

val jprop_names_update : Ident.NameEnv.t -> joined_prop -> joined_prop

val proplist_collapse_pre : Prop.prop list -> joined_prop list

val propset_collapse : Propset.propset -> Propset.propset

(** reduce the proset only based on implication checking. *)
val propset_collapse_impl : Propset.propset -> Propset.propset

(** [jprop_filter filter joinedprops] applies [filter] to the elements
    of [joindeprops] and applies it to the subparts if the result is
    [None]. Returns the most absract results which pass [filter]. *)
val jprop_filter : (joined_prop -> 'a option) -> joined_prop list -> 'a list

val jprop_map : (Prop.prop -> Prop.prop) -> joined_prop -> joined_prop


(** {2 Meet Operators} *)

(** [propset_meet_generate] generates new symbolic heaps (i.e., props) 
    by applying the partial meet operator, adds the generated heaps
    to the argument propset, and returns the resulting propset. *) 

val propset_meet_generate : Propset.propset -> Propset.propset
