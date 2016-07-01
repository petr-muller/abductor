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

open Sil
open Prop

module F = Format
module E = Error

(** {2 Sets of Propositions} *)

module PropSet =
  Set.Make(struct
    type t = prop 
    let compare = prop_compare
  end)

let propset_compare = PropSet.compare

(** Sets of propositions. *)
type propset = PropSet.t

(** Singleton set. *)
let propset_singleton p = 
  let ps = Prop.prop_expand p 
  in List.fold_left (fun pset' p' -> PropSet.add p' pset') PropSet.empty ps

(** Set union. *)
let propset_union = PropSet.union

(** Set membership *)
let propset_mem p = 
  PropSet.mem p 

(** Set intersection *)
let propset_inter = PropSet.inter

let propset_add p pset = 
  let ps = Prop.prop_expand p 
  in List.fold_left (fun pset' p' -> PropSet.add p' pset') pset ps 

(** Set difference. *)
let propset_diff =
  PropSet.diff

let propset_empty = PropSet.empty

(** Set emptiness check. *)
let propset_is_empty = PropSet.is_empty

(** Size of the set *)
let propset_size = PropSet.cardinal

let propset_filter = PropSet.filter

let proplist2propset plist =
  List.fold_right propset_add plist propset_empty

let propset2proplist pset =
  PropSet.elements pset

(** Apply function to all the elements of [propset], removing those where it returns [None]. *)
let propset_map_option f pset =
  let plisto = List.map f (propset2proplist pset) in
  let plisto = List.filter (function | Some _ -> true | None -> false) plisto in
  let plist = List.map (function Some p -> p | None -> assert false) plisto
  in proplist2propset plist

(** Apply function to all the elements of [propset]. *)
let propset_map f pset =
  proplist2propset (List.map f (propset2proplist pset))

(** [propset_fold f pset a] computes [f (... (f (f a p1) p2) ...) pn]
    where [p1 ... pN] are the elements of pset, in increasing order. *)
let propset_fold f a pset  =
  let l = propset2proplist pset
  in List.fold_left f a l

(** [propset_iter f pset] computes (f p1;f p2;..;f pN)
    where [p1 ... pN] are the elements of pset, in increasing order. *)
let propset_iter =
  PropSet.iter

let propset_subseteq =
  PropSet.subset

(** {2 Pretty print} *)

let pp_proplist f plist =
  let rec pp_seq_newline n f = function
    | [] -> ()
    | [x] -> F.fprintf f "PROP %d:@,@[%a@]" n pp_prop x
    | x::l -> F.fprintf f "PROP %d:@,@[%a@]@,@,%a" n pp_prop x (pp_seq_newline (n+1)) l 
  in F.fprintf f "@[<v>%a@]" (pp_seq_newline 1) plist


(** Pretty print a set of propositions. *)
let pp_propset f pset =
  let plist = propset2proplist pset 
  in pp_proplist f plist

(** dump a propset *)
let d_propset (ps:propset) = Error.add_print_action (Error.PTpropset, Obj.repr ps)

let pp_propset_compact = pp_propset

let pp_proplist_dotty f plist = 
  let _=Dotty.reset_proposition_counter () in
  let _ = F.fprintf f "\n\n\ndigraph main { \nnode [shape=box];\n" in
  let _ = F.fprintf f "\n compound = true; \n" in
  let _ = F.fprintf f "\n /* size=\"12,7\"; ratio=fill;*/ \n" in
  let _ = List.map (Dotty.pp_dotty f (Dotty.Generic_proposition)) plist
  in F.fprintf f  "\n}" 

let pp_propset_dotty f pset =
  let plist = propset2proplist pset
  in pp_proplist_dotty f plist

let pp_proplist_dotty_file filename plist =
  let outc = open_out filename in
  let fmt = F.formatter_of_out_channel outc in
  let _ = F.fprintf fmt "#### Dotty version:  ####@.%a@.@." pp_proplist_dotty plist
  in close_out outc

let pp_propset_dotty_file filename pset =
  let plist = propset2proplist pset
  in pp_proplist_dotty_file filename plist
