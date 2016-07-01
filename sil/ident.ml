(*
 *
 * Copyright (c) 2006-2008,
 *  Cristiano Calcagno    <ccris@doc.ic.ac.uk>
 *  Dino Distefano        <ddino@dcs.qmul.ac.uk>
 *  Peter O'Hearn         <ohearn@dcs.qmul.ac.uk>
 *  Hongseok Yang         <hyang@dcs.qmul.ac.uk>
 * All rights reserved.
 *)

(** Module for Names and Identifiers *)

module E = Error.MyErr (struct let mode = Error.DEFAULT end)

type name = int
type kind = int

let kprimed = -1
let knormal = 0
let kfootprint = 1

type ident =
    {kind: int;
     name: name;
     stamp: int}

(** {2 Comparison Functions} *)

let string_equal (s1:string) (s2:string) = s1=s2

let (=) (i:int) (j:int) = Pervasives.(=) i j
let (<>) (i:int) (j:int) = Pervasives.(<>) i j

(** Compare police: generic compare disabled. *)
let compare = ()

(** Efficient comparison for integers *)
let int_compare (i:int) (j:int) = i-j

let name_compare = int_compare

let name_equal (n1:name) (n2:name) = n1==n2

let kind_equal k1 k2 = k1==k2

let ident_compare i1 i2 =
  let n = i2.kind-i1.kind
  in if n<>0 then n
    else 
      let n = name_compare i1.name i2.name
      in if n<>0 then n
	else int_compare i1.stamp i2.stamp

let ident_equal i1 i2 =
  i1.stamp==i2.stamp && i1.kind==i2.kind && i1.name==i2.name (* most unlikely first *)

let rec ident_list_compare il1 il2 = match il1,il2 with
  | [],[] -> 0
  | [],_ -> -1
  | _,[] -> 1
  | i1::l1, i2::l2 ->
      let n = ident_compare i1 i2
      in if n<>0 then n
	else ident_list_compare l1 l2

let ident_list_equal ids1 ids2 = (ident_list_compare ids1 ids2 = 0)

(** {2 Conversion between Names and Strings} *)

module StringHash =
  Hashtbl.Make(struct
    type t = string
    let equal (s1:string) (s2:string) = string_equal s1 s2
    let hash = Hashtbl.hash
  end)

module NameHash =
  Hashtbl.Make(struct
    type t = name
    let equal = name_equal
    let hash = Hashtbl.hash
  end)

type string_name_map =
    { next_available_name: int ref;
      string_to_name: name StringHash.t;
      name_to_string: string NameHash.t }

(** Bijection between names and strings. *)
let string_name_map =
  { next_available_name = ref max_int;
    string_to_name = StringHash.create 1000;
    name_to_string = NameHash.create 1000}

(** Convert a string to a name using counter [next_available]. *)
let string_to_name (s:string) = 
  try StringHash.find string_name_map.string_to_name s
  with Not_found ->
    let name = !(string_name_map.next_available_name) in
      decr string_name_map.next_available_name;
      StringHash.add string_name_map.string_to_name s name;
      NameHash.add string_name_map.name_to_string name s;
      name

(** Convert a name to a string. *)
let name_to_string (name:name) =
  try
    NameHash.find string_name_map.name_to_string name
  with Not_found ->
    E.err "@.@.ERROR cannot find name %d@.@." name;
    assert false

module NameEnv =
struct
  type t = string NameHash.t

  (** [name_update env name] updates [name], which was defined using
      [env], to use (and possibly extend) the current environment *)
  let name_update (env:t) (name:name) : name =
    try
      let s = NameHash.find env name in
      let name' = string_to_name s
      in name'
    with Not_found ->
      E.err "@.ERROR: cannot find name: %s@." (name_to_string name);
      raise (Failure "Ident.name_update")

  let ident_update env id =
    try
      let s = NameHash.find env id.name in
      let name' = string_to_name s
      in {id with name=name'}
    with Not_found -> raise (Failure "Ident.ident_update")
end

(** {2 Functions and Hash Tables for Managing Stamps} *)

(** Set the stamp of the identifier *)
let ident_set_stamp i stamp =
  {i with stamp=stamp}

(** Get the stamp of the identifier *)
let ident_get_stamp i =
  i.stamp

(** Map from names to stamps. *)
let name_map = NameHash.create 1000

let create_ident kind name stamp =
  {kind=kind;name=name;stamp=stamp}

(** Generate a normal identifier with the given name and stamp *)
let create_normal_ident name stamp =
  {kind=knormal; name=name; stamp=stamp}

(** Generate a primed identifier with the given name and stamp *)
let create_primed_ident name stamp =
  {kind=kprimed; name=name; stamp=stamp}

(** Generate a footprint identifier with the given name and stamp *)
let create_footprint_ident name stamp =
  {kind=kfootprint; name=name; stamp=stamp}

(** {2 Functions for Identifiers} *)

(** Get a name of an identifier *)
let ident_name id =
  id.name

let ident_kind id =
  id.kind

let ident_is_primed (id:ident) =
  id.kind==kprimed

let ident_is_normal (id:ident) =
  id.kind==knormal 

let ident_is_footprint (id:ident) =
  id.kind==kfootprint

let make_ident_primed id =
  if id.kind==kprimed then assert false
  else {id with kind=kprimed}

let make_ident_unprimed id =
  if id.kind<>kprimed then assert false
  else {id with kind=knormal}

(** Create a fresh identifier with the given kind and name. *)
let create_fresh_ident kind name =
  let stamp =
    try
      let stamp = NameHash.find name_map name
      in NameHash.replace name_map name (stamp+1);
	stamp+1
    with Not_found ->
      NameHash.add name_map name 0;
      0
  in {kind=kind; name=name; stamp=stamp}

(** Create a fresh normal identifier with the given name. *)
let create_fresh_normal_ident name =
  create_fresh_ident knormal name

(** Create a fresh footprint identifier with the given name. *)
let create_fresh_footprint_ident name =
  create_fresh_ident kfootprint name

(** Create a fresh primed identifier with the given name. *)
let create_fresh_primed_ident name =
  create_fresh_ident kprimed name

(** Name used for tmp variables *)
let name_siltmp = string_to_name "siltmp"

(** {2 Pretty Printing} *)
open Format

(** Convert an identifier to a string. *)
let ident_to_string id =
  let base_name = name_to_string id.name in
  let prefix =
    if id.kind==kfootprint then "@"
    else if id.kind==knormal then ""
    else "_" in
  let suffix = "$" ^ (string_of_int id.stamp)
  in prefix ^ base_name ^ suffix

(** Print a sequence. *)
let rec pp_seq pp f = function
  | [] -> ()
  | [x] -> fprintf f "%a" pp x
  | x::l -> fprintf f "%a,%a" pp x (pp_seq pp) l

(** Pretty print a name. *)
let pp_name f name = fprintf f "%s" (name_to_string name)

(** Pretty print an identifier. *)
let pp_ident f id = fprintf f "%s" (ident_to_string id)

(** pretty printer for lists of identifiers *)
let rec pp_ident_list = pp_seq pp_ident

(** pretty printer for lists of names *)
let rec pp_name_list = pp_seq pp_name

module NameSet =
struct
  module M = Set.Make (struct type t = name let compare = name_compare end)
  type t = M.t ref
  let create () = ref M.empty
  let add nset name =
    nset := M.add name !nset
  let add_string nset (s:string) =
    nset := M.add (string_to_name s) !nset
  let add_ident nset id =
    nset := M.add id.name !nset
  let to_env (nset:t) : string NameHash.t =
    let env = NameHash.create 3 in
    let add_name_env name =
      NameHash.replace env name (name_to_string name) in
    let () = M.iter add_name_env !nset
    in env
  let pp fmt (nset:t) =
    M.iter (fun name -> Format.fprintf fmt "%a " pp_name name) !nset
end
