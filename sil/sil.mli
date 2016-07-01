(*
 *
 * Copyright (c) 2006-2008,
 *  Cristiano Calcagno    <ccris@doc.ic.ac.uk>
 *  Dino Distefano        <ddino@dcs.qmul.ac.uk>
 *  Peter O'Hearn         <ohearn@dcs.qmul.ac.uk>
 *  Hongseok Yang         <hyang@dcs.qmul.ac.uk>
 * All rights reserved.
 *)

(** The Smallfoot Intermediate Language *)

open Ident

(** Field names. *)
type fieldname = name

(** Nams for named types. *)
type typename = name 

(** {2 Programs and Types} *)

type pvar

(** Types for sil (structured) expressions. *)
type typ =
    | Tvar of typename  (** named type *)
    | Tint (** integer type *)
    | Tfloat (** float type *)
    | Tvoid (** void type *)
    | Tfun (** function type *)
    | Tptr of typ (** pointer type *)
    | Tstruct of (fieldname * typ) list (** structure type *)
    | Tarray of typ * int (** array type with fixed size *)

(** Program expressions. *)
type exp =
    | Var of ident (** pure variable: it is not an lvalue *)
    | Const_int of int  (** integer constants *)
    | Const_fun of name  (** function value *)
    | Cast of typ * exp  (** type cast *)
    | UnOp of Cil.unop * exp (** unary operator *)
    | BinOp of Cil.binop * exp * exp (** binary operator *)
    | Lvar of pvar  (** the address of a program variable *)
    | Lfield of exp * fieldname (** a field offset *)
    | Lindex of exp * exp (** an array index offset: [exp1\[exp2\]] *)
    | Sizeof of typ (** a sizeof expression *)

(** An instruction. *)
type instr =
    | Letderef of ident * exp * typ * Cil.location (** declaration [let x = *lexp:typ] *)
    | Set of exp * typ * exp * Cil.location (** assignment [*lexp1:typ = exp2] *)
    | Nullify of pvar * Cil.location (** nullify dead variable *)
    | Call of (exp * typ * typ) option * exp * (exp*typ) list * Cil.location
               (** function call [*lexp1 = (typ)exp2(exp(typ) list)] *) 

(** Offset for an lvalue. *)
type offset = Off_fld of fieldname | Off_index of exp

(** {2 Components of Propositions} *)

(** Structured expressions represent a value of structured type, such
    as an array or a struct. *)
type strexp =
    | Eexp of exp  (** Base case: normal expression *)
    | Estruct of (fieldname * strexp) list  (** C structure *)
    | Earray of int * (exp * strexp) list  (** Array of fixed size. *)

(** An atom is a pure atomic formula. *)
type atom =
    | Aeq of exp * exp (** equality *)
    | Aneq of exp * exp (** disequality*)

type lseg_kind =
    | Lseg_NE (** nonempty (possibly circular) listseg *)
    | Lseg_PE (** possibly empty (possibly circular) listseg *)

(** an atomic heap predicate *)

type hpred =
    | Hpointsto of exp * strexp * exp  (** represents [exp|->strexp:typexp] where [typexp] is an expression representing a type, e.h. [sizeof(t)]. *)
    | Hlseg of lseg_kind * hpara * exp * exp * exp list (** higher-order predicate for singly-linked lists. Should ensure that exp1!=exp2 implies that exp1 is allocated. This assumption is used in the rearrangement. The last [exp list] parameter
							    is used to denote the shared links by all the nodes in the list.*)
    | Hdllseg of lseg_kind * hpara_dll * exp * exp * exp * exp * exp list (** higher-order predicate for doubly-linked lists. *)

(** Parameter for the higher-order singly-linked list predicate. Means
    [lambda (root,next,svars). Exists evars. body].  Assume that
    [root],[next],[svars],[evars] are disjoint sets of primed identifiers,
    and include all the free primed identifiers in [body].  Assume that
    body does not contain any non-primed identifiers. *)
and hpara = 
    {root: ident;
     next: ident;
     svars: ident list;
     evars: ident list;
     body: hpred list}

and hpara_dll = 
    {cell: ident;  (** forward input *)
     blink: ident;  (** backward link *)
     flink: ident;  (** forward link *)
     svars_dll: ident list;
     evars_dll: ident list;
     body_dll: hpred list}



(** {2 Type Environment} *)

(** Look up a name in the global type environment. *)
val tenv_lookup : typename -> typ option

(** Add a (name,typ) pair to the global type environment. *)
val tenv_add : typename -> typ -> unit

(** {2 Comparision Functions} *)

val pvar_get_name : pvar -> name

(** Turn a pvar into a seed pvar (which stored the initial value) *)
val pvar_to_seed : pvar -> pvar

(** Check if the pvar is a seed var *)
val pvar_is_seed : pvar -> bool

val pvar_compare : pvar -> pvar -> int 

val pvar_equal : pvar -> pvar -> bool

val pvar_names_update : NameEnv.t -> pvar -> pvar

(** Comparision for fieldnames. *)
val fld_compare : fieldname -> fieldname -> int

(** Equality for fieldnames. *)
val fld_equal : fieldname -> fieldname -> bool

(** Comparision for types. *)
val typ_compare : typ -> typ -> int

(** Equality for types. *)
val typ_equal : typ -> typ -> bool

val unop_equal : Cil.unop -> Cil.unop -> bool

val binop_equal : Cil.binop -> Cil.binop -> bool

val exp_compare : exp -> exp -> int

val exp_equal : exp -> exp -> bool

val exp_list_equal : exp list -> exp list -> bool

val atom_compare : atom -> atom -> int

val atom_equal : atom -> atom -> bool

val strexp_compare : strexp -> strexp -> int

val strexp_equal : strexp -> strexp -> bool

val hpara_compare : hpara -> hpara -> int

val hpara_equal : hpara -> hpara -> bool

val hpara_dll_compare : hpara_dll -> hpara_dll -> int

val hpara_dll_equal : hpara_dll -> hpara_dll -> bool

val lseg_kind_compare : lseg_kind -> lseg_kind -> int

val lseg_kind_equal : lseg_kind -> lseg_kind -> bool

val hpred_compare : hpred -> hpred -> int

val hpred_equal : hpred -> hpred -> bool

val fld_strexp_compare : fieldname * strexp -> fieldname * strexp -> int

val fld_strexp_list_compare : (fieldname * strexp) list  -> (fieldname * strexp) list -> int

val exp_strexp_compare : exp * strexp -> exp * strexp -> int

(** {2 Pretty Printing} *)

(** Pretty print a list of elements *)
val pp_seq : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a list -> unit

(** Pretty print a location. *)
val pp_loc : Format.formatter -> Cil.location -> unit

(** Dump a location. *)
val d_loc : Cil.location -> unit

(** Pretty print a type. *)
val pp_typ : Format.formatter -> typ -> unit

(** Pretty print a type with all the details. *)
val pp_typ_full : Format.formatter -> typ -> unit

(** Dump a type with all the details. *)
val d_typ_full : typ -> unit

(** Dump a list of types. *)
val d_typ_list : typ list -> unit

(** Pretty print a program variable. *)
val pp_pvar : Format.formatter -> pvar -> unit

(** Dump a program variable. *)
val d_pvar : pvar -> unit

(** Pretty print a list of program variables. *)
val pp_pvar_list : Format.formatter -> pvar list -> unit

(** Pretty print an expression. *)
val pp_exp : Format.formatter -> exp -> unit

(** dump an expression. *)
val d_exp : exp -> unit

(** Pretty print a type with all the details. *)
val pp_texp_full : Format.formatter -> exp -> unit

(** Dump a type expression with all the details. *)
val d_texp_full : exp -> unit

(** Pretty print a list of expressions. *)
val pp_exp_list : Format.formatter -> exp list -> unit

(** Dump a list of expressions. *)
val d_exp_list : exp list -> unit

(** Pretty print an offset *)
val pp_offset : Format.formatter -> offset -> unit

(** Dump an offset *)
val d_offset : offset -> unit

(** Pretty print a list of offsets *)
val pp_offset_list : Format.formatter -> offset list -> unit

(** Dump a list of offsets *)
val d_offset_list : offset list -> unit

(** Pretty print an instruction. *)
val pp_instr : Format.formatter -> instr -> unit

(** Dump an instruction. *)
val d_instr : instr -> unit

(** Pretty print a list of instructions. *)
val pp_instr_list : Format.formatter -> instr list -> unit

(** Dump a list of instructions. *)
val d_instr_list : instr list -> unit

(** Pretty print an atom. *)
val pp_atom : Format.formatter -> atom -> unit

(** Dump an atom. *)
val d_atom : atom -> unit

(** Pretty print a strexp. *)
val pp_sexp : Format.formatter -> strexp -> unit

(** Dump a strexp. *)
val d_sexp : strexp -> unit

(** Pretty print a hpred. *)
val pp_hpred : Format.formatter -> hpred -> unit

(** Dump a hpred. *)
val d_hpred : hpred -> unit

(** Pretty print a hpred. *)
val pp_hpred_list : Format.formatter -> hpred list -> unit

(** Pretty print a hpara. *)
val pp_hpara : Format.formatter -> hpara -> unit

(** Pretty print a dll_hpara. *)
val pp_dll_hpara : Format.formatter -> hpara_dll -> unit

(** {2 Functions for traversing SIL data types} *) 


(** Change exps in strexp by [f]. *)
(** WARNING: the result might not be normalized. *)
val strexp_expmap : (exp -> exp) -> strexp -> strexp

(** Change exps in hpred by [f]. *)
(** WARNING: the result might not be normalized. *)
val hpred_expmap : (exp -> exp) -> hpred -> hpred

(** Change exps in hpred list by [f]. *)
(** WARNING: the result might not be normalized. *)
val hpred_list_expmap : (exp -> exp) -> hpred list -> hpred list

(** Change exps in atom by [f]. *)
(** WARNING: the result might not be normalized. *)
val atom_expmap : (exp -> exp) -> atom -> atom

(** Change exps in atom list by [f]. *)
(** WARNING: the result might not be normalized. *)
val atom_list_expmap : (exp -> exp) -> atom list -> atom list

(** {2 Function for computing lexps in sigma} *) 

val sigma_get_lexps : (exp -> bool) -> hpred list -> exp list

(** {2 Utility Functions for Expressions} *)

(** Return the root of [lexp]. *)
val root_of_lexp : exp -> exp

(** Get an expression "undefined" *)
val exp_get_undefined : unit -> exp

(** Checks whether an expression denotes a location using pointer arithmetic. 
    Currently, catches array-indexing expressions such as a[i] only. *)
val exp_pointer_arith : exp -> bool


(** {2 Functions for computing program variables} *)

val exp_fpv : exp -> pvar list

val strexp_fpv : strexp -> pvar list

val atom_fpv : atom -> pvar list

val hpred_fpv : hpred -> pvar list

val hpara_fpv : hpara -> pvar list


(** {2 Functions for computing free non-program variables} *)

(** Type of free variables. These include primed, normal and footprint variables. We keep a count of how many types the variables appear. *)
type fav

(** Pretty print a fav. *)
val pp_fav : Format.formatter -> fav -> unit

(** Create a new [fav]. *)
val fav_new : unit -> fav

(** Emptyness check. *)
val fav_is_empty : fav -> bool

(** Check whether a predicate holds for all elements. *)
val fav_for_all : fav -> (ident -> bool) -> bool

(** Check whether a predicate holds for some elements. *)
val fav_exists : fav -> (ident -> bool) -> bool

(** Membership test fot [fav] *)
val fav_mem : fav -> ident -> bool

(** Convert a list to a fav. *)
val fav_from_list : ident list -> fav

(** Convert a [fav] to a sorted list of identifiers without repetitions. *)
val fav_to_list : fav -> ident list

(** Convert a [fav] to a list of identifiers while preserving the order
that identifiers were added to [fav]. *)
val fav_to_list_stable : fav -> ident list

(** Copy a [fav]. *)
val fav_copy : fav -> fav

(** Turn a xxx_fav_add function into a xxx_fav function *)
val fav_imperative_to_functional : (fav -> 'a -> unit) -> 'a -> fav

(** [fav_filter_ident fav f] only keeps [id] if [f id] is true. *)
val fav_filter_ident : fav -> (ident->bool) -> unit

(** Like [fav_filter_ident] but return a copy. *)
val fav_copy_filter_ident : fav -> (ident->bool) -> fav

(** [fav_subset_ident fav1 fav2] returns true if every ident in [fav1]
    is in [fav2].*)
val fav_subset_ident : fav -> fav -> bool

val ident_list_fav_add : ident list -> fav -> unit

(** [exp_fav_add fav exp] extends [fav] with the free variables of [exp] *)
val exp_fav_add : fav -> exp -> unit

val exp_fav : exp -> fav

val ident_in_exp : ident -> exp -> bool


val strexp_fav_add : fav -> strexp -> unit

val atom_fav_add : fav -> atom -> unit

val atom_fav: atom -> fav

val hpred_fav_add : fav -> hpred -> unit

val hpara_fav_add : fav -> hpara -> unit

(** Variables in hpara, excluding bound vars in the body *)
val hpara_shallow_av : hpara -> fav

(** Variables in hpara_dll, excluding bound vars in the body *)
val hpara_dll_shallow_av : hpara_dll -> fav

(** {2 Functions for computing all free or bound non-program variables} *)

(** Non-program variables include all of primed, normal and footprint
    variables. Thus, the functions essentially compute all the
    identifiers occuring in a parameter. Some variables can appear more 
    than once in the result. *)

val exp_av_add : fav -> exp -> unit

val strexp_av_add : fav -> strexp -> unit

val atom_av_add : fav -> atom -> unit

val hpred_av_add : fav -> hpred -> unit

val hpara_av_add : fav -> hpara -> unit

(** {2 Substitution} *)

type subst

(** Create a substitution from a list of pairs. *)
val sub_of_list : (ident * exp) list -> subst

(** Convert a subst to a list of pairs. *)
val sub_to_list : subst -> (ident * exp) list

(** The empty substitution. *)
val sub_empty : subst

(** Comparison for substitutions. *)
val sub_compare : subst -> subst -> int

(** Equality for substitutions. *) 
val sub_equal : subst -> subst -> bool

(** Join two substitutions into one. *)
val sub_join : subst -> subst -> subst

(** [sub_find filter sub] returns the expression associated to the first identifier that satisfies [filter]. Raise [Not_found] if there isn't one. *)
val sub_find : (ident->bool) -> subst -> exp

(** [sub_filter filter sub] restricts the domain of [sub] to the
    identifiers satisfying [filter]. *)
val sub_filter : (ident -> bool) -> subst -> subst

(** [sub_filter_exp filter sub] restricts the domain of [sub] to the
    identifiers satisfying [filter(id,sub(id))]. *)
val sub_filter_pair : (ident * exp -> bool) -> subst -> subst

(** [sub_range_partition filter sub] partitions [sub] according to
    whether range expressions satisfy [filter]. *)
val sub_range_partition : (exp -> bool) -> subst -> subst*subst

(** [sub_domain_partition filter sub] partitions [sub] according to
    whether domain identifiers satisfy [filter]. *)
val sub_domain_partition : (ident -> bool) -> subst -> subst*subst

(** Return the list of identifiers in the domain of the substitution. *)
val sub_domain : subst -> ident list

(** Return the list of expressions in the range of the substitution. *)
val sub_range : subst -> exp list

(** [sub_range_map f sub] applies [f] to the expressions in the range of [sub]. *)
val sub_range_map : (exp -> exp) -> subst-> subst

(** [sub_map f g sub] applies the renaming [f] to identifiers in the domain
of [sub] and the substitution [g] to the expressions in the range of [sub]. *)
val sub_map : (ident -> ident) -> (exp -> exp) -> subst -> subst

(** Extend substitution and return [None] if not possible. *)
val extend_sub : subst -> ident -> exp -> subst option

(** Free auxilary variables in the domain and range of the
    substitution. *)
val sub_fav_add : fav -> subst -> unit

(** Free or bound auxilary variables in the domain and range of the
    substitution. *)
val sub_av_add : fav -> subst -> unit

(** substitution functions *)
(** WARNING: these functions do not ensure that the results are normalized. *)
val exp_sub : subst -> exp -> exp

val strexp_sub : subst -> strexp -> strexp

val atom_sub : subst -> atom -> atom

val hpred_sub : subst -> hpred -> hpred

val hpara_sub : subst -> hpara -> hpara

val typ_names_add : NameSet.t -> typ -> unit

val typ_names_update : NameEnv.t -> typ -> typ

val exp_names_add : NameSet.t -> exp -> unit

val exp_names_update : NameEnv.t -> exp -> exp

val sub_names_add : NameSet.t -> subst -> unit

val sub_names_update : NameEnv.t -> subst -> subst

(** {2 Functions for replacing occurrences of expressions.} *)

(** The first parameter should define a partial function.
    No parts of hpara are replaced by these functions. *)

val exp_replace_exp : (exp * exp) list -> exp -> exp

val strexp_replace_exp : (exp * exp) list -> strexp -> strexp

val atom_replace_exp : (exp * exp) list -> atom -> atom

val hpred_replace_exp : (exp * exp) list -> hpred -> hpred

(** {2 Functions for constructing or destructing entities in this module} *)

val mk_pvar : name -> Cil.fundec -> string -> pvar

val mk_pvar_global : name -> pvar

val pvar_add_suffix : pvar -> string -> pvar

(** Compute the offset list of an expression *)
val exp_get_offsets : exp -> offset list

val sigma_to_sigma_ne : hpred list -> (atom list * hpred list) list

(** [hpara_instantiate para e1 e2 elist] instantiates [para] with [e1],
    [e2] and [elist].  If [para = lambda (x,y,xs). exists zs. b],
    then the result of the instantiation is [b\[e1/x,e2/y,elist/xs,_zs'/zs\]] 
    for some fresh [_zs'].*)
val hpara_instantiate : hpara -> exp -> exp -> exp list -> ident list * hpred list

(** [hpara_dll_instantiate para cell blink flink  elist] instantiates [para] with [cell],
    [blink], [flink],  and [elist].  If [para = lambda (x,y,z,xs). exists zs. b],
    then the result of the instantiation is [b\[cell/x, blink/y, flink/z, elist/xs,_zs'/zs\]] 
    for some fresh [_zs'].*)
val hpara_dll_instantiate : hpara_dll -> exp  -> exp -> exp -> exp list -> ident list * hpred list
