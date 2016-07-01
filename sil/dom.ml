(*
 *
 * Copyright (c) 2006-2008,
 *  Cristiano Calcagno    <ccris@doc.ic.ac.uk>
 *  Dino Distefano        <ddino@dcs.qmul.ac.uk>
 *  Peter O'Hearn         <ohearn@dcs.qmul.ac.uk>
 *  Hongseok Yang         <hyang@dcs.qmul.ac.uk>
 *  Oukseh Lee            <olee@dcs.qmul.ac.ul>
 * All rights reserved.
 *)


(** Join Operator *)

open Ident
open Sil
open Format
open Prop
open Prover
open Propset
open Match

module S = Sil
module E = Error.MyErr (struct let mode = Error.DEFAULT end)
(*let () = E.set_mode Error.ALWAYS
let () = E.set_colour Error.red*)

type pi = atom list
type sigma = hpred list

type join_mode = Pre | Post

exception Fail



(** {2 Utility Functions for Ids} *)

let can_rename id =
  ident_is_primed id || ident_is_footprint id



(** {2 Utility Functions for Lists} *)

let list_is_empty = function
  | [] -> ()
  | _::_ -> raise Fail

(** Returns (reverse input_list)@acc *)
let rec list_rev_with_acc acc = function
  | [] -> acc
  | x::xs -> list_rev_with_acc (x::acc) xs

(** The function works on sorted lists without duplicates *)
let rec list_merge_sorted_nodup compare res xs1 xs2 = 
  match xs1, xs2 with
  | [], _ -> 
      list_rev_with_acc xs2 res
  | _, [] -> 
      list_rev_with_acc xs1 res
  | x1::xs1', x2::xs2' ->
      let n = compare x1 x2 in
      if n = 0 then 
        list_merge_sorted_nodup compare (x1::res) xs1' xs2'
      else if n < 0 then
        list_merge_sorted_nodup compare (x1::res) xs1' xs2
      else
        list_merge_sorted_nodup compare (x2::res) xs1 xs2'

let list_map2 f l1 l2 =
  let rec go l1 l2 acc =
    match l1,l2 with
    | [],[] -> List.rev acc
    | x1::l1', x2::l2' ->
	let x' = f x1 x2 in
	go l1' l2' (x'::acc) 
    | _ -> raise Fail in
  go l1 l2 []


(** {2 Utility Functions for Sigma} *)

let sigma_equal sigma1 sigma2 = 
  let rec f sigma1_rest sigma2_rest = 
    match (sigma1_rest, sigma2_rest) with
      | [], [] -> ()
      | [], _::_ | _::_, [] -> raise Fail
      | hpred1::sigma1_rest', hpred2::sigma2_rest' ->
	  if hpred_equal hpred1 hpred2 then f sigma1_rest' sigma2_rest'
	  else raise Fail in
  let sigma1_sorted = List.sort hpred_compare sigma1 in
  let sigma2_sorted = List.sort hpred_compare sigma2 
  in f sigma1_sorted sigma2_sorted 

let sigma_get_start_lexps_sort sigma = 
  let exp_compare_neg e1 e2 = - (exp_compare e1 e2) in
  let filter e = fav_for_all (exp_fav e) ident_is_normal  in
  let lexps = sigma_get_lexps filter sigma in 
  List.sort exp_compare_neg lexps 

(** {2 Utility Functions for Side} *)

type side = Lhs | Rhs

let select side e1 e2 = 
  match side with
  | Lhs -> e1
  | Rhs -> e2

let opposite side =
  match side with
  | Lhs -> Rhs
  | Rhs -> Lhs

let do_side side f e1 e2 =
  match side with 
  | Lhs -> f e1 e2
  | Rhs -> f e2 e1 



(** {2 Various Sets} *)

module Eset = Set.Make
  (struct
    type t = exp
    let compare = exp_compare
  end)

let elist_to_eset es =
  List.fold_left (fun set e -> Eset.add e set) Eset.empty es

module Iset = Set.Make
  (struct
    type t = ident
    let compare = ident_compare
  end)

let ilist_to_iset ids =
  List.fold_left (fun set id -> Iset.add id set) Iset.empty ids

module EPset = Set.Make
  (struct
    type t = exp * exp  
    let compare (e1,e1') (e2,e2') = 
      match (exp_compare e1 e2) with
      | i when i <> 0 -> i
      | _ -> exp_compare e1' e2'
  end)

let epset_add e e' set =
  match (exp_compare e e') with
  | i when i <= 0 -> EPset.add (e,e') set 
  | _ -> EPset.add (e',e) set



(** {2 Module for worklist} *)

module Todo = struct

  type t = (exp * exp * exp) list

  exception Empty

  let tbl = ref []

  let set todo = tbl := todo
  let push e = match e with
    | Const_int _, Const_int _, _ -> () (* Constants are not locations *)
    | _ -> tbl := e :: !tbl
  let reset () = tbl := []
  let take () = let res = !tbl in reset(); res
  let pop () = 
    match !tbl with 
    | h::t -> tbl := t; h
    | _ -> raise Empty

end

type todo = Todo.t



(** {2 Module for maintaining information about noninjectivity during join} *)

module NonInj = struct

  (* mappings from Var exps to Var exps *)
  let equiv_tbl1 = Hashtbl.create 32
  let equiv_tbl2 = Hashtbl.create 32

  (* mappings from Var exps to Lvar or Const_int exps *)
  let const_tbl1 = Hashtbl.create 32
  let const_tbl2 = Hashtbl.create 32

  let reset () = 
    Hashtbl.clear equiv_tbl1;
    Hashtbl.clear equiv_tbl2;
    Hashtbl.clear const_tbl1;
    Hashtbl.clear const_tbl2

  let init () = reset ()
  let final () = reset ()

  let lookup' tbl e default = 
    match e with
    | Var _ ->
      begin
        try 
          Hashtbl.find tbl e
        with Not_found -> 
          Hashtbl.replace tbl e default;
          default 
      end
    | _ -> assert false

  let lookup_equiv' tbl e =
    lookup' tbl e e

  let lookup_const' tbl e =
    lookup' tbl e Eset.empty 

  let rec find' tbl e =
    let e' = lookup_equiv' tbl e in
    match e' with
    | Var _ ->
        if exp_equal e e' then e
        else
          begin 
            let root = find' tbl e' in
            Hashtbl.replace tbl e root;
            root
          end
    | _ -> assert false

  let union' tbl const_tbl e1 e2 = 
    let r1 = find' tbl e1 in
    let r2 = find' tbl e2 in
    let new_r, old_r = 
      match (exp_compare r1 r2) with
      | i when i <= 0 -> r1, r2
      | _ -> r2, r1 in
    let new_c = lookup_const' const_tbl new_r in
    let old_c = lookup_const' const_tbl old_r in
    let res_c = Eset.union new_c old_c in
    if Eset.cardinal res_c > 1 then raise Fail;
    Hashtbl.replace tbl old_r new_r;
    Hashtbl.replace const_tbl new_r res_c

  let replace_const' tbl const_tbl e c =
    let r = find' tbl e in
    let set = Eset.add c (lookup_const' const_tbl r) in
    if Eset.cardinal set > 1 then raise Fail;
    Hashtbl.replace const_tbl r set  

  let add side e e' =
    let tbl, const_tbl = 
      match side with 
      | Lhs -> equiv_tbl1, const_tbl1 
      | Rhs -> equiv_tbl2, const_tbl2 
    in
    match e, e' with
    | Var id, Var id' ->
        begin
          match can_rename id, can_rename id' with
          | true, true -> union' tbl const_tbl e e'
          | true, false -> replace_const' tbl const_tbl e e' 
          | false, true -> replace_const' tbl const_tbl e' e 
          | _ -> raise Fail
        end
    | Var id, Const_int _ | Var id, Lvar _ ->
        if (can_rename id) then replace_const' tbl const_tbl e e'  
        else raise Fail
    | Const_int _, Var id' | Lvar _, Var id' ->
        if (can_rename id') then replace_const' tbl const_tbl e' e 
        else raise Fail
    | _ ->
        if not (exp_equal e e') then raise Fail 
        else ()

  let check side es = 
    let f = function 
      | Var id -> can_rename id
      | _ -> false in
    let vars, nonvars = List.partition f es in
    let tbl, const_tbl = 
      match side with 
      | Lhs -> equiv_tbl1, const_tbl1 
      | Rhs -> equiv_tbl2, const_tbl2 
    in
    if (List.length nonvars > 1) then false
    else 
      match vars, nonvars with
      | [], _ | [_], [] -> true
      | v::vars', _ ->
          let r = find' tbl v in
          let set = lookup_const' const_tbl r in
          (List.for_all (fun v' -> exp_equal (find' tbl v') r) vars') &&
          (List.for_all (fun c -> Eset.mem c set) nonvars)
end



(** {2 Modules for checking whether join or meet loses too much info} *)

module type InfoLossCheckerSig =
sig
  val init : sigma -> sigma -> unit
  val final : unit -> unit
  val lost_little : side -> exp -> exp list -> bool   
end

module Dangling = struct

  let lexps1 = ref Eset.empty
  let lexps2 = ref Eset.empty

  let get_lexp_set' sigma = 
    let lexp_lst = sigma_get_lexps (fun _ -> true) sigma in
    List.fold_left (fun set e -> Eset.add e set) Eset.empty lexp_lst

  let init sigma1 sigma2 = 
    lexps1 := get_lexp_set' sigma1;
    lexps2 := get_lexp_set' sigma2

  let final () =
    lexps1 := Eset.empty;
    lexps2 := Eset.empty

  (* conservatively checks whether e is dangling *)
  let check side e =
    let lexps = 
      match side with 
      | Lhs -> !lexps1 
      | Rhs -> !lexps2 
    in
    match e with
    | Var id -> can_rename id && not (Eset.mem e lexps)
    | _ -> false 
end


module CheckJoinPre : InfoLossCheckerSig = struct

  let init sigma1 sigma2 =
    NonInj.init ();
    Dangling.init sigma1 sigma2

  let final () =
    NonInj.final ();
    Dangling.final ()

  let fail_case' side e es =
    let side_op = opposite side in
    match e with
    | Lvar _ -> false
    | Var id when ident_is_normal id -> List.length es >= 1
    | Var id -> 
        if !Config.join_cond = 0 then 
          List.exists (exp_equal (Const_int 0)) es 
        else if Dangling.check side e then 
          begin
            E.log "@[.... Dangling Check (dang e:%a) (? es:%a) ....@\n@." pp_exp e pp_exp_list es;
            List.exists (fun e' -> not (Dangling.check side_op e')) es
          end
        else
          begin
            E.log "@[.... Dangling Check (nondang e:%a) (? es:%a) ....@\n@." pp_exp e pp_exp_list es;
            List.exists (Dangling.check side_op) es
          end 
    | _ -> false

  let lost_little side e es =
    let side_op = opposite side in
    let es = match e with Const_int _ -> [] | _ -> es in
    if (fail_case' side e es) then false
    else 
      match es with
      | [] | [_] -> true
      | _ -> (NonInj.check side_op es) 
end


module CheckJoinPost : InfoLossCheckerSig = struct

  let init sigma1 sigma2 =
    NonInj.init ()

  let final () =
    NonInj.final ()

  let fail_case' side e es = 
    match e with
    | Lvar _ -> false
    | Var id when ident_is_normal id -> List.length es >= 1
    | Var id -> false
    | _ -> false

  let lost_little side e es =
    let side_op = opposite side in
    let es = match e with Const_int _ -> [] | _ -> es in
    if (fail_case' side e es) then false
    else 
      match es with
      | [] | [_] -> true
      | _ -> NonInj.check side_op es 
end


module CheckMeet : InfoLossCheckerSig = struct

  let lexps1 = ref Eset.empty
  let lexps2 = ref Eset.empty

  let init sigma1 sigma2 =
    let lexps1_lst = sigma_get_lexps (fun _ -> true) sigma1 in
    let lexps2_lst = sigma_get_lexps (fun _ -> true) sigma2 in
    lexps1 := elist_to_eset lexps1_lst;
    lexps2 := elist_to_eset lexps2_lst

  let final () = 
    lexps1 := Eset.empty;
    lexps2 := Eset.empty

  let lost_little side e es =
    let lexps = match side with 
      | Lhs -> !lexps1 
      | Rhs -> !lexps2 
    in
    match es, e with
    | [], _ -> 
        true
    | [Const_int _], Lvar _ -> 
        false
    | [Const_int _], Var _ -> 
        not (Eset.mem e lexps)
    | [Const_int _], _ ->
        assert false
    | [_], Lvar _ | [_], Var _ -> 
        true
    | [_], _ ->
        assert false
    | _, Lvar _ | _, Var _ -> 
        false
    | _, Const_int _ -> 
        assert false
    | _ -> assert false
end



(** {2 Modules for renaming} *)

module Rename = struct

  type t = (exp * exp * exp) list

  let tbl = ref []

  let init () = tbl := []
  let final () = tbl := []
  let set r = tbl := r
  let get () = !tbl
  let push v = tbl := v :: !tbl

  let empty = []

  let check' e1 e2 =
    try
      let eq_to_e (f1, f2, _) = exp_equal e1 f1 && exp_equal e2 f2 in
      let _, _, res = List.find eq_to_e !tbl in
      res
    with Not_found -> raise Fail

  let check e1 e2 =
    let no_fav1 = not (fav_exists (exp_fav e1) can_rename) in
    let no_fav2 = not (fav_exists (exp_fav e2) can_rename) in
    if (no_fav1 && no_fav2) then
      if (exp_equal e1 e2) then e1 else raise Fail
    else
      check' e1 e2

  let check_noninj' lost_little side e = 
    let side_op = opposite side in
    let assoc_es = 
      match e with
      | Const_int _ -> [] 
      | Lvar _ | Var _ ->
          let is_same_e (e1,e2,_) = exp_equal e (select side e1 e2) in 
          let assoc = List.filter is_same_e !tbl in
          List.map (fun (e1,e2,_) -> select side_op e1 e2) assoc 
      | _ -> assert false 
    in
    lost_little side e assoc_es
         
  let check_noninj lost_little =
    let lhs_es = List.map (fun (e1,_,_) -> e1) !tbl in
    let rhs_es = List.map (fun (_,e2,_) -> e2) !tbl in
    (List.for_all (check_noninj' lost_little Rhs) rhs_es) &&
    (List.for_all (check_noninj' lost_little Lhs) lhs_es) 
 
  let lookup_side' side e  =
    let f (e1,e2,_) = exp_equal e (select side e1 e2) in
    List.filter f !tbl

  (* Return the triple whose side is [e], if it exists unique *)
  let lookup' todo side e : exp =
    match e with
    | Var id when can_rename id ->
	begin
	  let r = lookup_side' side e in 
	  match r with
	  | [(e1, e2, id) as t] -> if todo then Todo.push t; id
	  | _ -> raise Fail
	end
    | Var _ | Const_int _ | Lvar _ -> if todo then Todo.push (e, e, e); e
    | _ -> raise Fail

  let lookup side e = lookup' false side e
  let lookup_todo side e = lookup' true side e
  let lookup_list side l = List.map (lookup side) l
  let lookup_list_todo side l = List.map (lookup_todo side) l

  let to_subst_proj (side: side) vars =
    let renaming_restricted =
      List.filter (function (_, _, Var i) -> fav_mem vars i | _ -> assert false) !tbl in
    let sub_list_side = 
      List.map 
	(function (e1, e2, Var i) -> (i, select side e1 e2) | _ -> assert false)
	renaming_restricted in
    let sub_list_side_sorted = 
      List.sort (fun (i,e) (i',e') -> exp_compare e e') sub_list_side in
    let rec find_duplicates = 
      function
	| (i,e)::((i',e')::l' as t) -> exp_equal e e' || find_duplicates t
	| _ -> false in 
    if find_duplicates sub_list_side_sorted then raise Fail
    else sub_of_list sub_list_side

  let to_subst_emb (side : side) = 
    let renaming_restricted =
      let pick_id_case (e1, e2, e) =
        match select side e1 e2 with
        | Var i -> can_rename i
        | _ -> false in
      List.filter pick_id_case !tbl in
    let sub_list = 
      let project (e1, e2, e) = 
        match select side e1 e2 with
        | Var i -> (i, e)
        | _ -> assert false in
      List.map project renaming_restricted in
    let sub_list_sorted = 
      let compare (i,_) (i',_) = ident_compare i i' in
      List.sort compare sub_list in
    let rec find_duplicates = function
      | (i,_)::((i',_)::l' as t) -> ident_equal i i' || find_duplicates t
      | _ -> false in 
    if find_duplicates sub_list_sorted then raise Fail
    else sub_of_list sub_list_sorted

  let get_others side e = 
    let side_op = opposite side in
    let r = lookup_side' side e in 
    match r with
    | [] -> None
    | [(e1, e2, e')] -> Some (e', select side_op e1 e2) 
    | _ -> None

  (* Extend the renaming relation. At least one of e1 and e2 
   * should be a primed or footprint variable *)
  let extend e1 e2 default_op =
    try
      check' e1 e2
    with Fail ->
      let no_fav1 = not (fav_exists (exp_fav e1) can_rename) in
      let no_fav2 = not (fav_exists (exp_fav e2) can_rename) in
      let e = 
        if (no_fav1 && no_fav2) then
          if (exp_equal e1 e2) then e1 else raise Fail
        else
          match default_op with
	  | None -> Var (Ident.create_fresh_primed_ident Ident.name_siltmp) 
          | Some e -> e in
      let entry = e1, e2, e in
      push entry;
      Todo.push entry;
      e 

  let rec pp_seq' pp f = function
    | [] -> ()
    | [x] -> fprintf f "%a" pp x
    | x::l -> fprintf f "%a %a" pp x (pp_seq pp) l
	
  let pp f renaming =
    let pp_triple f (e1,e2,e3) = fprintf f "(%a,%a,%a)" pp_exp e3 pp_exp e1 pp_exp e2
    in (pp_seq' pp_triple) f renaming

end

type renaming = Rename.t



(** {2 Functions for constructing fresh sil data types} *)

let extend_side' side e =
  match Rename.get_others side e with
  | None ->
      let e_op = Var (Ident.create_fresh_primed_ident Ident.name_siltmp) in
      let e1, e2 = 
        match side with
        | Lhs -> e, e_op
        | Rhs -> e_op, e in
      Rename.extend e1 e2 None 
  | Some (e',_) -> e' 

let rec exp_construct_fresh side e =
  match e with
  | Var id -> 
      if ident_is_normal id then 
      begin
        Todo.push (e,e,e); 
        e
      end
      else extend_side' side e
  | Const_int _ | Const_fun _ -> e 
  | Cast (t,e1) ->
      let e1' = exp_construct_fresh side e1 in
      Cast (t,e1')
  | UnOp(unop,e1) ->
      let e1' = exp_construct_fresh side e1 in
      UnOp(unop,e1')
  | BinOp(binop,e1,e2) ->
      let e1' = exp_construct_fresh side e1 in
      let e2' = exp_construct_fresh side e2 in
      BinOp(binop,e1',e2')
  | Lvar _ ->
      e
  | Lfield(e1,fld) ->
      let e1' = exp_construct_fresh side e1 in
      Lfield(e1',fld) 
  | Lindex(e1,e2) ->
      let e1' = exp_construct_fresh side e1 in
      let e2' = exp_construct_fresh side e2 in
      Lindex(e1',e2')
  | Sizeof _ ->
      e

let strexp_construct_fresh side =
  Sil.strexp_expmap (exp_construct_fresh side)

let hpred_construct_fresh side = 
  Sil.hpred_expmap (exp_construct_fresh side)



(** {2 Join and Meet for Ids} *)

let ident_same_kind_primed_footprint id1 id2 =
  (ident_is_primed id1 && ident_is_primed id2) || 
  (ident_is_footprint id1 && ident_is_footprint id2)

let ident_partial_join (id1:ident) (id2:ident) =
  match ident_is_normal id1, ident_is_normal id2 with
  | true, true -> 
      if ident_equal id1 id2 then Var id1 
      else raise Fail
  | true, _ | _, true ->
      Rename.extend (Var id1) (Var id2) None
  | _ ->
      if ident_same_kind_primed_footprint id1 id2 then 
        Rename.extend (Var id1) (Var id2) None
      else raise Fail

let ident_partial_meet (id1:ident) (id2:ident) =
  match ident_is_normal id1, ident_is_normal id2 with
  | true, true -> 
      if ident_equal id1 id2 then Var id1 
      else raise Fail
  | true, _ ->
      let e1, e2 = Var id1, Var id2 in
      Rename.extend e1 e2 (Some e1)
  | _, true ->
      let e1, e2 = Var id1, Var id2 in
      Rename.extend e1 e2 (Some e2) 
  | _ ->
      if ident_same_kind_primed_footprint id1 id2 then 
        Rename.extend (Var id1) (Var id2) None
      else raise Fail



(** {2 Join and Meet for Exps} *)

let rec exp_partial_join (e1:exp) (e2:exp) : exp =
  match e1, e2 with
  | Var id1, Var id2 -> ident_partial_join id1 id2
  | Var id, Const_int n 
  | Const_int n, Var id ->
      if not (ident_is_normal id) then
          Rename.extend e1 e2 None
      else raise Fail
      (* 
      if not (ident_is_normal id) && n=0 then
          Rename.extend e1 e2 None
      else raise Fail
      *)
  | Const_int n1, Const_int n2 ->
      if n1 <> n2 then 
        if (!Config.abs_val >= 2) then S.exp_get_undefined ()
        else raise Fail 
      else e1
  | Cast(t1,e1), Cast(t2,e2) ->
      if not (typ_equal t1 t2) then raise Fail
      else
	let e1'' = exp_partial_join e1 e2 in
	Cast (t1, e1'')
  | UnOp(unop1,e1), UnOp(unop2,e2) ->
      if not (unop_equal unop1 unop2) then raise Fail
      else UnOp (unop1, exp_partial_join e1 e2)
  | BinOp(binop1,e1,e1'), BinOp(binop2,e2,e2') ->
      if not (binop_equal binop1 binop2) then raise Fail
      else 
	let e1'' = exp_partial_join e1 e2 in
        let e2'' = exp_partial_join e1' e2' in
	BinOp(binop1,e1'',e2'')
  | Var id, Lvar _
  | Lvar _, Var id ->
      if not (ident_is_normal id) then
          Rename.extend e1 e2 None
      else raise Fail
  | Lvar(pvar1), Lvar(pvar2) ->
      if not (pvar_equal pvar1 pvar2) then raise Fail
      else e1
  | Lfield(e1,f1), Lfield(e2,f2) ->
      if not (fld_equal f1 f2) then raise Fail
      else Lfield(exp_partial_join e1 e2, f1)
  | Lindex(e1,e1'), Lindex(e2,e2') ->
      let e1'' = exp_partial_join e1 e2 in
      let e2'' = exp_partial_join e1' e2' in
      Lindex(e1'',e2'')
  | _ -> raise Fail

let rec exp_partial_meet (e1:exp) (e2:exp) : exp =
  match e1, e2 with
  | Var id1, Var id2 -> 
      ident_partial_meet id1 id2
  | Var id, Const_int n -> 
      if not (ident_is_normal id) then
          Rename.extend e1 e2 (Some e2)
      else raise Fail
  | Const_int n, Var id ->
      if not (ident_is_normal id) then
          Rename.extend e1 e2 (Some e1)
      else raise Fail
  | Const_int n1, Const_int n2 ->
      if n1 <> n2 then raise Fail 
      else e1
  | Cast(t1,e1), Cast(t2,e2) ->
      if not (typ_equal t1 t2) then raise Fail
      else
	let e1'' = exp_partial_meet e1 e2 in
	Cast (t1, e1'')
  | UnOp(unop1,e1), UnOp(unop2,e2) ->
      if not (unop_equal unop1 unop2) then raise Fail
      else UnOp (unop1, exp_partial_meet e1 e2)
  | BinOp(binop1,e1,e1'), BinOp(binop2,e2,e2') ->
      if not (binop_equal binop1 binop2) then raise Fail
      else 
	let e1'' = exp_partial_meet e1 e2 in
        let e2'' = exp_partial_meet e1' e2' in
	BinOp(binop1,e1'',e2'')
  | Var id, Lvar _ ->
      if not (ident_is_normal id) then
          Rename.extend e1 e2 (Some e2)
      else raise Fail
  | Lvar _, Var id ->
      if not (ident_is_normal id) then
          Rename.extend e1 e2 (Some e1)
      else raise Fail
  | Lvar(pvar1), Lvar(pvar2) ->
      if not (pvar_equal pvar1 pvar2) then raise Fail
      else e1
  | Lfield(e1,f1), Lfield(e2,f2) ->
      if not (fld_equal f1 f2) then raise Fail
      else Lfield(exp_partial_meet e1 e2, f1)
  | Lindex(e1,e1'), Lindex(e2,e2') ->
      let e1'' = exp_partial_meet e1 e2 in
      let e2'' = exp_partial_meet e1' e2' in
      Lindex(e1'',e2'')
  | _ -> raise Fail

let exp_list_partial_join = list_map2 exp_partial_join

let exp_list_partial_meet = list_map2 exp_partial_meet



(** {2 Join and Meet for Strexp} *)

let rec strexp_partial_join (strexp1:strexp) (strexp2:strexp) : strexp =

  let rec f_fld_se_list fld_se_list_acc fld_se_list1 fld_se_list2 =
    match fld_se_list1, fld_se_list2 with
    | [], _ | _, [] -> 
	let strexp_res = Estruct (List.rev fld_se_list_acc) in
	strexp_res
    | (fld1,se1)::fld_se_list1', (fld2,se2)::fld_se_list2' ->
	let comparison = fld_compare fld1 fld2 in 
	if comparison < 0 then
	  f_fld_se_list fld_se_list_acc fld_se_list1' fld_se_list2 
	else if comparison > 0 then
	  f_fld_se_list fld_se_list_acc fld_se_list1 fld_se_list2'
	else 
	  let strexp' = strexp_partial_join se1 se2 in
	  let fld_se_list_new = (fld1, strexp') :: fld_se_list_acc in 
	  f_fld_se_list fld_se_list_new fld_se_list1' fld_se_list2' in

  let rec f_idx_se_list size idx_se_list_acc idx_se_list1 idx_se_list2 = 
    match idx_se_list1, idx_se_list2 with
    | [], _ | _, [] -> Earray (size, List.rev idx_se_list_acc)
    | (idx1,se1)::idx_se_list1', (idx2,se2)::idx_se_list2' ->
	let idx = Rename.check idx1 idx2 in
	let strexp' = strexp_partial_join se1 se2 in
 	let idx_se_list_new = (idx, strexp') :: idx_se_list_acc in
	f_idx_se_list size idx_se_list_new idx_se_list1' idx_se_list2' in

  match strexp1, strexp2 with
  | Eexp e1, Eexp e2 -> Eexp (exp_partial_join e1 e2)
  | Estruct fld_se_list1, Estruct fld_se_list2 ->
      f_fld_se_list [] fld_se_list1 fld_se_list2
  | Earray (size1, idx_se_list1), Earray (size2, idx_se_list2) 
      when size1 = size2 ->
      f_idx_se_list size1 [] idx_se_list1 idx_se_list2
  | _ -> raise Fail

let rec strexp_partial_meet (strexp1:strexp) (strexp2:strexp) : strexp =

  let construct side rev_list ref_list =
    let construct_offset_se (off, se) = (off, strexp_construct_fresh side se) in
    let acc = List.map construct_offset_se ref_list in
    list_rev_with_acc acc rev_list in 
 
  let rec f_fld_se_list fld_se_list_acc fld_se_list1 fld_se_list2 =
    match fld_se_list1, fld_se_list2 with
    | [], _ -> 
        Estruct (construct Rhs fld_se_list_acc fld_se_list2) 
    | _, [] -> 
	Estruct (construct Lhs fld_se_list_acc fld_se_list1) 
    | (fld1,se1)::fld_se_list1', (fld2,se2)::fld_se_list2' ->
	let comparison = fld_compare fld1 fld2 in 
	if comparison < 0 then
          let se' = strexp_construct_fresh Lhs se1 in
          let fld_se_list_acc' = (fld1,se')::fld_se_list_acc in
	  f_fld_se_list fld_se_list_acc' fld_se_list1' fld_se_list2 
	else if comparison > 0 then
          let se' = strexp_construct_fresh Rhs se2 in
          let fld_se_list_acc' = (fld2,se')::fld_se_list_acc in
	  f_fld_se_list fld_se_list_acc' fld_se_list1 fld_se_list2'
	else 
	  let strexp' = strexp_partial_meet se1 se2 in
	  let fld_se_list_new = (fld1, strexp') :: fld_se_list_acc in 
	  f_fld_se_list fld_se_list_new fld_se_list1' fld_se_list2' in

  let rec f_idx_se_list size idx_se_list_acc idx_se_list1 idx_se_list2 = 
    match idx_se_list1, idx_se_list2 with
    | [], _ ->
        Earray (size, construct Rhs idx_se_list_acc idx_se_list2)
    | _, [] -> 
        Earray (size, construct Lhs idx_se_list_acc idx_se_list1)
    | (idx1,se1)::idx_se_list1', (idx2,se2)::idx_se_list2' ->
	let idx = Rename.check idx1 idx2 in
	let strexp' = strexp_partial_meet se1 se2 in
 	let idx_se_list_new = (idx, strexp') :: idx_se_list_acc in
	f_idx_se_list size idx_se_list_new idx_se_list1' idx_se_list2' in
 
  match strexp1, strexp2 with
  | Eexp e1, Eexp e2 -> Eexp (exp_partial_meet e1 e2)
  | Estruct fld_se_list1, Estruct fld_se_list2 ->
      f_fld_se_list [] fld_se_list1 fld_se_list2
  | Earray (size1, idx_se_list1), Earray (size2, idx_se_list2) 
      when size1 = size2 ->
      f_idx_se_list size1 [] idx_se_list1 idx_se_list2
  | _ -> raise Fail



(** {2 Join and Meet for kind, hpara, hpara_dll} *)
	
let kind_join k1 k2 = match k1,k2 with
  | Lseg_PE,_ -> Lseg_PE
  | _,Lseg_PE -> Lseg_PE
  | Lseg_NE,Lseg_NE -> Lseg_NE

let kind_meet k1 k2 = match k1,k2 with
  | Lseg_NE,_ -> Lseg_NE
  | _,Lseg_NE -> Lseg_NE
  | Lseg_PE,Lseg_PE -> Lseg_PE

let hpara_partial_join (hpara1:hpara) (hpara2:hpara) : hpara =
  if hpara_match_with_impl true hpara2 hpara1 then 
    hpara1
  else if hpara_match_with_impl true hpara1 hpara2 then 
    hpara2
  else 
    raise Fail

let hpara_partial_meet (hpara1:hpara) (hpara2:hpara) : hpara =
  if hpara_match_with_impl true hpara2 hpara1 then
    hpara2
  else if hpara_match_with_impl true hpara1 hpara2 then
    hpara1
  else
    raise Fail

let hpara_dll_partial_join (hpara1:hpara_dll) (hpara2:hpara_dll) : hpara_dll =
  if hpara_dll_match_with_impl true hpara2 hpara1 then 
    hpara1
  else if hpara_dll_match_with_impl true hpara1 hpara2 then 
    hpara2
  else 
    raise Fail

let hpara_dll_partial_meet (hpara1:hpara_dll) (hpara2:hpara_dll) : hpara_dll =
  if hpara_dll_match_with_impl true hpara2 hpara1 then 
    hpara2
  else if hpara_dll_match_with_impl true hpara1 hpara2 then 
    hpara1
  else 
    raise Fail



(** {2 Join and Meet for hpred} *)

let hpred_partial_join (todo:exp*exp*exp) (hpred1:hpred) (hpred2:hpred) : hpred =
  let e1, e2, e = todo in
  match hpred1, hpred2 with 
  | Hpointsto (e1, se1, te1), Hpointsto (e2, se2, te2) when exp_equal te1 te2 -> 
      mk_ptsto e (strexp_partial_join se1 se2) te1  
  | Hpointsto _, _ | _, Hpointsto _ ->
      raise Fail
  | Hlseg (k1,hpara1,root1,next1,shared1), Hlseg (k2,hpara2,root2,next2,shared2) ->
      let hpara' = hpara_partial_join hpara1 hpara2 in
      let next' = exp_partial_join next1 next2 in
      let shared' = exp_list_partial_join shared1 shared2 in
      mk_lseg (kind_join k1 k2) hpara' e next' shared' 
  | Hdllseg (k1,para1,iF1,oB1,oF1,iB1,shared1), 
    Hdllseg (k2,para2,iF2,oB2,oF2,iB2,shared2) ->
      let fwd1 = exp_equal e1 iF1 in
      let fwd2 = exp_equal e2 iF2 in
      let hpara' = hpara_dll_partial_join para1 para2 in
      let iF',iB' = 
        if (fwd1 && fwd2) then (e, exp_partial_join iB1 iB2) 
        else if (not fwd1 && not fwd2) then (exp_partial_join iF1 iF2, e)
        else raise Fail in
      let oF' = exp_partial_join oF1 oF2 in
      let oB' = exp_partial_join oB1 oB2 in
      let shared' = exp_list_partial_join shared1 shared2 in
      mk_dllseg (kind_join k1 k2) hpara' iF' oB' oF' iB' shared'
  | _ ->
      assert false

let hpred_partial_meet (todo:exp*exp*exp) (hpred1:hpred) (hpred2:hpred) : hpred =
  let e1, e2, e = todo in
  match hpred1, hpred2 with 
  | Hpointsto (e1, se1, te1), Hpointsto (e2, se2, te2) when exp_equal te1 te2 -> 
      mk_ptsto e (strexp_partial_meet se1 se2) te1  
  | Hpointsto _, _ | _, Hpointsto _ ->
      raise Fail
  | Hlseg (k1,hpara1,root1,next1,shared1), Hlseg (k2,hpara2,root2,next2,shared2) ->
      let hpara' = hpara_partial_meet hpara1 hpara2 in
      let next' = exp_partial_meet next1 next2 in
      let shared' = exp_list_partial_meet shared1 shared2 in
      mk_lseg (kind_meet k1 k2) hpara' e next' shared' 
  | Hdllseg (k1,para1,iF1,oB1,oF1,iB1,shared1), 
    Hdllseg (k2,para2,iF2,oB2,oF2,iB2,shared2) ->
      let fwd1 = exp_equal e1 iF1 in
      let fwd2 = exp_equal e2 iF2 in
      let hpara' = hpara_dll_partial_meet para1 para2 in
      let iF',iB' = 
        if (fwd1 && fwd2) then (e, exp_partial_meet iB1 iB2) 
        else if (not fwd1 && not fwd2) then (exp_partial_meet iF1 iF2, e)
        else raise Fail in
      let oF' = exp_partial_meet oF1 oF2 in
      let oB' = exp_partial_meet oB1 oB2 in
      let shared' = exp_list_partial_meet shared1 shared2 in
      mk_dllseg (kind_meet k1 k2) hpara' iF' oB' oF' iB' shared'
  | _ ->
      assert false



(** {2 Join and Meet for Sigma} *)

let find_hpred_by_address (e:exp) (sigma:sigma) : hpred option * sigma =
  let is_root_for_e e' = 
    match (is_root prop_emp e' e) with
    | None -> false
    | Some _ -> true in
  let contains_e = function
    | Hpointsto (e',_,_) -> is_root_for_e e'
    | Hlseg (_,_,e',_,_) -> is_root_for_e e'
    | Hdllseg (_,_,iF,_,_,iB,_) -> is_root_for_e iF || is_root_for_e iB in
  let rec f sigma_acc = function 
    | [] -> None, sigma
    | hpred::sigma ->
	if contains_e hpred then 
	  Some hpred, (List.rev sigma_acc) @ sigma
	else
	  f (hpred::sigma_acc) sigma in
  f [] sigma

let same_pred (hpred1:hpred) (hpred2:hpred) : bool =
  match hpred1, hpred2 with
  | Hpointsto _, Hpointsto _ -> true
  | Hlseg _, Hlseg _ -> true
  | Hdllseg _, Hdllseg _ -> true
  | _ -> false

(* check that applying renaming to the lhs/rhs of [sigma_new] 
 * gives [sigma] and that the renaming is injective *)

let sigma_renaming_check (lhs:side) (sigma:sigma) (sigma_new:sigma) =
  (* apply the lhs/rhs of the renaming to sigma, 
   * and check that the renaming of primed vars is injective *)
  let fav_sigma = sigma_fav sigma_new in
  let sub = Rename.to_subst_proj lhs fav_sigma in
  let sigma' = sigma_sub sub sigma_new in
  sigma_equal sigma sigma'

let sigma_renaming_check_lhs = sigma_renaming_check Lhs
let sigma_renaming_check_rhs = sigma_renaming_check Rhs

let rec sigma_partial_join' (sigma_acc:sigma) 
    (sigma1_in:sigma) (sigma2_in:sigma) : (sigma * sigma * sigma)  =
  
  let lookup_and_expand side e e' =
    match (Rename.get_others side e, side) with
    | None, _ -> raise Fail
    | Some(e_res, e_op), Lhs -> (e_res, exp_partial_join e' e_op)
    | Some(e_res, e_op), Rhs -> (e_res, exp_partial_join e_op e') in

  let join_list_and_non side root' hlseg e opposite =
    match hlseg with
    | Hlseg (_, hpara, root, next, shared) ->
	let next' = do_side side exp_partial_join next opposite in
        let shared' = Rename.lookup_list side shared in
        NonInj.add side root next;
        Hlseg (Lseg_PE, hpara, root', next', shared') 

    | Hdllseg (k, hpara, iF, oB, oF, iB, shared) 
      when exp_equal iF e ->
	let oF' = do_side side exp_partial_join oF opposite in
        let shared' = Rename.lookup_list side shared in
        let oB', iB' = lookup_and_expand side oB iB in 
        (* 
        let oB' = Rename.lookup side oB in
        let iB' = Rename.lookup side iB in 
        *)
        NonInj.add side iF oF;
        NonInj.add side oB iB;
        Hdllseg (Lseg_PE, hpara, root', oB', oF', iB', shared') 

    | Hdllseg (k, hpara, iF, oB, oF, iB, shared) 
      when exp_equal iB e ->
	let oB' = do_side side exp_partial_join oB opposite in
        let shared' = Rename.lookup_list side shared in
        let oF', iF' = lookup_and_expand side oF iF in 
        (*
        let oF' = Rename.lookup side oF in
        let iF' = Rename.lookup side iF in
        *)
        NonInj.add side iF oF;
        NonInj.add side oB iB;
        Hdllseg (Lseg_PE, hpara, iF', oB', oF', root', shared') 

    | _ -> assert false in 

  let update_list side lseg root' =
    match lseg with
    | Hlseg (k, hpara, _, next, shared) ->
	let next' = Rename.lookup side next
	and shared' = Rename.lookup_list_todo side shared in
	Hlseg (k, hpara, root', next', shared')
    | _ -> assert false in

  let update_dllseg side dllseg iF iB =
    match dllseg with
    | Hdllseg (k, hpara, _, oB, oF, _, shared) ->
	let oB' = Rename.lookup side oB 
	and oF' = Rename.lookup side oF 
	and shared' = Rename.lookup_list_todo side shared in
	Hdllseg (k, hpara, iF, oB', oF', iB, shared')
    | _ -> assert false in

  (* Drop the part of 'other' sigma corresponding to 'target' sigma if possible.
     'side' describes that target is Lhs or Rhs.
     'todo' describes the start point. *)

  let cut_sigma side todo (target:sigma) (other:sigma) =
    let x = Todo.take () in
    Todo.push todo;
    let res = 
      match side with
      | Lhs -> 
	  let res, target', other' = sigma_partial_join' [] target other in
	  list_is_empty target';
	  sigma_renaming_check_lhs target res;
	  other'
      | Rhs -> 
	  let res, other', target' = sigma_partial_join' [] other target in
	  list_is_empty target';
	  sigma_renaming_check_rhs target res;
	  other' in
    Todo.set x;
    res in

  let cut_lseg side todo lseg sigma =
    match lseg with
    | Hlseg (_, hpara, root, next, shared) ->
	let _, sigma_lseg = hpara_instantiate hpara root next shared in 
	cut_sigma side todo sigma_lseg sigma
    | _ -> assert false in

  let cut_dllseg side todo root lseg sigma =
    match lseg with
    | Hdllseg (_, hpara, _, oB, oF, _, shared) ->
	let _, sigma_dllseg = hpara_dll_instantiate hpara root oB oF shared in
	cut_sigma side todo sigma_dllseg sigma
    | _ -> assert false in

  try
    let todo_curr = Todo.pop () in
    let e1, e2, e = todo_curr in
    E.log "@[<2>.... sigma_partial_join' ....@\n";
    E.log "@\nTODO: %a,%a,%a@\n" Sil.pp_exp e1 Sil.pp_exp e2 Sil.pp_exp e;
    E.log "@\nPROP1=%a@\n" pp_sigma sigma1_in;
    E.log "@\nPROP2=%a@\n@." pp_sigma sigma2_in; 
    let hpred_opt1, sigma1 = find_hpred_by_address e1 sigma1_in in
    let hpred_opt2, sigma2 = find_hpred_by_address e2 sigma2_in in
    match hpred_opt1, hpred_opt2 with
    | None, None ->
        sigma_partial_join' sigma_acc sigma1 sigma2

    | Some (Hlseg (k, _, _, _, _) as lseg), None 
    | Some (Hdllseg (k, _, _, _, _, _, _) as lseg), None -> 
        if (not !Config.nelseg) || (lseg_kind_equal k Lseg_PE) then
          let sigma_acc' = join_list_and_non Lhs e lseg e1 e2 :: sigma_acc in 
  	  sigma_partial_join' sigma_acc' sigma1 sigma2
        else
          raise Fail

    | None, Some (Hlseg (k, _, _, _, _) as lseg) 
    | None, Some (Hdllseg (k, _, _, _, _, _, _) as lseg) ->
        if (not !Config.nelseg) || (lseg_kind_equal k Lseg_PE) then
	  let sigma_acc' = join_list_and_non Rhs e lseg e2 e1 :: sigma_acc in
	  sigma_partial_join' sigma_acc' sigma1 sigma2
        else
          raise Fail 

    | None, _ | _, None -> raise Fail 
      
    | Some (hpred1), Some (hpred2) when same_pred hpred1 hpred2 ->
	let hpred_res1 = hpred_partial_join todo_curr hpred1 hpred2 in
        sigma_partial_join' (hpred_res1::sigma_acc) sigma1 sigma2

    | Some (Hlseg _ as lseg), Some (hpred2) ->
	let sigma2' = cut_lseg Lhs todo_curr lseg (hpred2::sigma2) in
        let sigma_acc' = update_list Lhs lseg e :: sigma_acc in
	sigma_partial_join' sigma_acc' sigma1 sigma2'

    | Some (hpred1), Some (Hlseg _ as lseg) ->
	let sigma1' = cut_lseg Rhs todo_curr lseg (hpred1::sigma1) in
        let sigma_acc' = update_list Rhs lseg e :: sigma_acc in
	sigma_partial_join' sigma_acc' sigma1' sigma2

    | Some (Hdllseg (_, _, iF1, _, _, iB1, _) as dllseg), Some (hpred2) 
      when exp_equal e1 iF1 ->
	let iB_res = exp_partial_join iB1 e2 in 
        let sigma2' = cut_dllseg Lhs todo_curr iF1 dllseg (hpred2::sigma2) in
	let sigma_acc' = update_dllseg Lhs dllseg e iB_res :: sigma_acc in
        NonInj.add Lhs iF1 iB1; (* add equality iF1=iB1 *)
	sigma_partial_join' sigma_acc' sigma1 sigma2'

    | Some (Hdllseg (_, _, iF1, _, _,iB1, _) as dllseg), Some (hpred2) 
	(* when exp_equal e1 iB1 *) ->
	let iF_res = exp_partial_join iF1 e2 in 
        let sigma2' = cut_dllseg Lhs todo_curr iB1 dllseg (hpred2::sigma2) in
	let sigma_acc' = update_dllseg Lhs dllseg iF_res e :: sigma_acc in
        NonInj.add Lhs iF1 iB1; (* add equality iF1=iB1 *)
	sigma_partial_join' sigma_acc' sigma1 sigma2'

    | Some (hpred1), Some (Hdllseg (_, _, iF2, _, _, iB2, _) as dllseg) 
      when exp_equal e2 iF2 ->
	let iB_res = exp_partial_join e1 iB2 in 
        let sigma1' = cut_dllseg Rhs todo_curr iF2 dllseg (hpred1::sigma1) in
	let sigma_acc' = update_dllseg Rhs dllseg e iB_res ::sigma_acc in
        NonInj.add Rhs iF2 iB2; (* add equality iF2=iB2 *)
	sigma_partial_join' sigma_acc' sigma1' sigma2

    | Some (hpred1), Some (Hdllseg (_, _, iF2, _, _, iB2, _) as dllseg) ->
	let iF_res = exp_partial_join e1 iF2 in 
        let sigma1' = cut_dllseg Rhs todo_curr iB2 dllseg (hpred1::sigma1) in
	let sigma_acc' = update_dllseg Rhs dllseg iF_res e :: sigma_acc in
        NonInj.add Rhs iF2 iB2; (* add equality iF2=iB2 *)
	sigma_partial_join' sigma_acc' sigma1' sigma2

    | Some (Hpointsto _), Some (Hpointsto _) ->
	  assert false (* Should be handled by a guarded case *)

  with Todo.Empty ->
    match sigma1_in, sigma2_in with
    | _::_, _::_ -> raise Fail
    | _ ->          sigma_acc, sigma1_in, sigma2_in 

let sigma_partial_join (mode:join_mode)  
    (sigma1:sigma) (sigma2:sigma) (todo:todo) : (sigma * sigma * sigma)  =

  let lost_little = match mode with
    | Post -> 
        CheckJoinPost.init sigma1 sigma2; 
        CheckJoinPost.lost_little 
    | Pre -> 
        CheckJoinPre.init sigma1 sigma2; 
        CheckJoinPre.lost_little in

  Rename.init (); Rename.set Rename.empty; Todo.set todo;

  let s1, s2, s3 = sigma_partial_join' [] sigma1 sigma2 in

  if Rename.check_noninj lost_little then 
      (s1, s2, s3) 
  else 
    raise Fail

let rec sigma_partial_meet' (sigma_acc:sigma) 
  (sigma1_in:sigma) (sigma2_in:sigma) : sigma =

(*
  let expand_lseg root lseg sigma =
    match lseg with
    | Hlseg (_, hpara, _, next, shared) ->
	let _, sigma_lseg = hpara_instantiate hpara root next shared in 
	sigma_lseg @ sigma
    | Hdllseg (_, hpara, _, oB, oF, _, shared) ->
	let _, sigma_dllseg = hpara_dll_instantiate hpara root oB oF shared in
	sigma_dllseg @ sigma
    | _ -> 
        assert false in
*)

  try
    let todo_curr = Todo.pop () in
    let e1, e2, e = todo_curr in
    E.log "@[<2>.... sigma_partial_meet' ....@\n";
    E.log "@\nTODO: %a,%a,%a@\n" Sil.pp_exp e1 Sil.pp_exp e2 Sil.pp_exp e;
    E.log "@\nPROP1=%a@\n" pp_sigma sigma1_in;
    E.log "@\nPROP2=%a@\n@." pp_sigma sigma2_in; 
    let hpred_opt1, sigma1 = find_hpred_by_address e1 sigma1_in in
    let hpred_opt2, sigma2 = find_hpred_by_address e2 sigma2_in in
    match hpred_opt1, hpred_opt2 with
    | None, None ->
        sigma_partial_meet' sigma_acc sigma1 sigma2

    | Some hpred, None ->
        let hpred' = hpred_construct_fresh Lhs hpred in
        let sigma_acc' = hpred' :: sigma_acc in
        sigma_partial_meet' sigma_acc' sigma1 sigma2
      
    | None, Some hpred ->
        let hpred' = hpred_construct_fresh Rhs hpred in
        let sigma_acc' = hpred' :: sigma_acc in
        sigma_partial_meet' sigma_acc' sigma1 sigma2

    | Some (hpred1), Some (hpred2) when same_pred hpred1 hpred2 ->
	let hpred' = hpred_partial_meet todo_curr hpred1 hpred2 in
        sigma_partial_meet' (hpred'::sigma_acc) sigma1 sigma2

    | Some _, Some _ ->
        raise Fail

  (* Hongseok : I comment out the code below, because it strengthens 
   * givem sigmas too much in some cases. It is better to fail in
   * those cases. 
   *)
  (*
    | Some (Hlseg _ as lseg1), Some _ ->
        let sigma1' = expand_lseg e1 lseg1 sigma1 in
        Todo.push todo_curr;
	sigma_partial_meet' sigma_acc sigma1' sigma2_in

    | Some _, Some (Hlseg _ as lseg2) ->
	let sigma2' = expand_lseg e2 lseg2 sigma2 in
        Todo.push todo_curr;
	sigma_partial_meet' sigma_acc sigma1_in sigma2'

    | Some (Hdllseg _ as dllseg1), Some (hpred2) ->
        let sigma1' = expand_lseg e1 dllseg1 sigma1 in
        Todo.push todo_curr;
        sigma_partial_meet' sigma_acc sigma1' sigma2_in

    | Some (hpred1), Some (Hdllseg _ as dllseg2) ->
        let sigma2' = expand_lseg e2 dllseg2 sigma2 in
        Todo.push todo_curr;
        sigma_partial_meet' sigma_acc sigma1_in sigma2'

    | Some (Hpointsto _), Some (Hpointsto _) ->
	assert false (* Should be handled by a guarded case *)
  *)

  with Todo.Empty ->
    match sigma1_in, sigma2_in with
    | [], [] -> sigma_acc
    | _, _ -> raise Fail

let sigma_partial_meet (sigma1:sigma) (sigma2:sigma) 
  (todos:todo) : sigma =
  Rename.init (); 
  Rename.set Rename.empty; 
  Todo.set todos;
  sigma_partial_meet' [] sigma1 sigma2



(** {2 Join and Meet for Pi} *)

let pi_partial_join (p:prop) (p1:prop) (p2:prop) : prop = 
  let is_const = function 
    (* | Var id -> ident_is_normal id *)
    | Const_int _ -> true 
    (* | Lvar _ -> true *)
    | _ -> false in

  let handle_atom_neq side p_op set a =
    match a with
    | Aneq(e, e') when (is_const e && is_const e') ->
        if not (check_disequal p_op e e') then set
        else epset_add e e' set
    | Aneq(Var id, e') | Aneq(e', Var id) 
      when (ident_is_normal id && is_const e') ->
        if not (check_disequal p_op (Var id) e') then set
        else epset_add (Var id) e' set 
    | Aneq(Var id, e') | Aneq(e', Var id) 
      when (is_const e') ->
        begin
          match (Rename.get_others side (Var id)) with
          | None -> set
          | Some (e_res, e_op) -> 
              if not (check_disequal p_op e_op e') then set
              else epset_add e_res e' set
        end
    | _ -> set in

  let pi1 = prop_get_pi p1 in
  let pi2 = prop_get_pi p2 in
  let neq_set1 = 
    List.fold_left (handle_atom_neq Lhs p2) EPset.empty pi1 in
  let neq_set = 
    List.fold_left (handle_atom_neq Rhs p1) neq_set1 pi2 
  in
  EPset.fold (fun (e,e') p' -> 
    conjoin_neq e e' p') neq_set p

let pi_partial_meet (p:prop) (p1:prop) (p2:prop) : prop = 
  let sub1 = Rename.to_subst_emb Lhs in
  let sub2 = Rename.to_subst_emb Rhs in

  let dom1 = ilist_to_iset (sub_domain sub1) in
  let dom2 = ilist_to_iset (sub_domain sub2) in

  let handle_atom sub dom atom =
    let fav_list = fav_to_list (atom_fav atom) in
    if List.for_all (fun id -> Iset.mem id dom) fav_list then
      atom_sub sub atom
    else raise Fail in
  let f1 p' atom = 
    prop_atom_and p' (handle_atom sub1 dom1 atom) in
  let f2 p' atom  =
    prop_atom_and p' (handle_atom sub2 dom2 atom) in

  let pi1 = prop_get_pi p1 in
  let pi2 = prop_get_pi p2 in

  let p_pi1 = List.fold_left f1 p pi1 in
  let p_pi2 = List.fold_left f2 p_pi1 pi2 in
  if (check_inconsistency_base p_pi2) then raise Fail
  else p_pi2 



(** {2 Join and Meet for Prop} *)

let prop_partial_join' (mode:join_mode) (p1:prop) (p2:prop) : prop =

  let sigma1 = prop_get_sigma p1 in
  let sigma2 = prop_get_sigma p2 in

  let es1 = sigma_get_start_lexps_sort sigma1 in
  let es2 = sigma_get_start_lexps_sort sigma2 in

  let simple_check = List.length es1 = List.length es2 in 
  let rec expensive_check es1' es2' = match (es1',es2') with
    | [], [] -> true
    | [], _::_ | _::_, [] -> false
    | e1::es1'', e2::es2'' -> 
	exp_equal e1 e2 && expensive_check es1'' es2'' in
  let sub_check _ = 
    let sub1 = prop_get_sub p1 in
    let sub2 = prop_get_sub p2 in 
    let range1 = sub_range sub1 in
    let f e = fav_for_all (exp_fav e) ident_is_normal in
    sub_equal sub1 sub2 && List.for_all f range1
  in
 
  if not (simple_check && expensive_check es1 es2 && sub_check ()) then 
    raise Fail
  else 
    let todos = List.map (fun x -> (x,x,x)) es1 in
    match sigma_partial_join mode sigma1 sigma2 todos with
    | sigma_new, [], [] ->
        let p = prop_replace_sigma sigma_new p1 in
        let p' = prop_replace_pi [] p in 
        pi_partial_join p' p1 p2 
    | _ -> raise Fail

let prop_partial_join_mode mode p1 p2 = 
  try Some (prop_partial_join' mode p1 p2) 
  with Fail -> None

let prop_partial_join = prop_partial_join_mode Post

let prop_partial_meet' (p1:prop) (p2:prop) : prop =

  let sigma1 = prop_get_sigma p1 in
  let sigma2 = prop_get_sigma p2 in

  let es1 = sigma_get_start_lexps_sort sigma1 in
  let es2 = sigma_get_start_lexps_sort sigma2 in
  let es = list_merge_sorted_nodup exp_compare [] es1 es2 in

  let sub_check _ = 
    let sub1 = prop_get_sub p1 in
    let sub2 = prop_get_sub p2 in 
    let range1 = sub_range sub1 in
    let f e = fav_for_all (exp_fav e) ident_is_normal in
    sub_equal sub1 sub2 && List.for_all f range1 in

  if not (sub_check ()) then 
    raise Fail
  else 
    let todos = List.map (fun x -> (x,x,x)) es in
    let sigma_new = sigma_partial_meet sigma1 sigma2 todos in
    let p = prop_replace_sigma sigma_new p1 in
    let p' = prop_replace_pi [] p in 
    let p'' = pi_partial_meet p' p1 p2
    in prop_rename_primed_footprint_vars p''

let prop_partial_meet p1 p2 =
  try (Some (prop_partial_meet' p1 p2))
  with Fail -> None



(** {2 Join and Meet for Propset} *)

type joined_prop =
    | Prop of prop
    | Joined of prop * joined_prop * joined_prop

let jprop_to_prop = function
  | Prop p -> p
  | Joined (p,_,_) -> p

(** Print the toplevel prop *)
let pp_jprop_short f jp =
  pp_prop f (jprop_to_prop jp)

(** Dump the toplevel prop *)
let d_jprop_short (jp:joined_prop) = Error.add_print_action (Error.PTjprop_short, Obj.repr jp)

(** Number the props in the list and print the join info using the numbering *)
let pp_jprop_list f jplist =
  let seq_number = ref 0 in
  let rec pp_seq_newline f = function
    | [] -> ()
    | [Prop p] -> incr seq_number; fprintf f "PROP %d: %a@\n" !seq_number pp_prop p
    | [Joined (p,p1,p2)] ->
	let () = pp_seq_newline f [p1] in
	let n1 = !seq_number in
	let () = pp_seq_newline f [p2] in
	let n2 = !seq_number in
	let () = incr seq_number
	in fprintf f "PROP %d (join of %d,%d): %a@\n" !seq_number n1 n2 pp_prop p
    | jp::l ->
	pp_seq_newline f [jp];
	pp_seq_newline f l in 

   pp_seq_newline f jplist; 
   fprintf f "@."

(** dump a joined prop list *)
let d_jprop_list (jplist:joined_prop list) = Error.add_print_action (Error.PTjprop_list, Obj.repr jplist)

(** Comparison for joined_prop *)
let rec jprop_compare jp1 jp2 = match jp1,jp2 with
  | Prop p1, Prop p2 ->
      prop_compare p1 p2
  | Prop _, _ -> -1
  | _, Prop _ -> 1
  | Joined (p1,jp1,jq1), Joined (p2,jp2,jq2) ->
      let n = prop_compare p1 p2
      in if n<>0 then n
	else let n = jprop_compare jp1 jp2
	  in if n<>0 then n
	    else jprop_compare jq1 jq2

(** Return true if the two join_prop's are equal *)
let jprop_equal jp1 jp2 =
  jprop_compare jp1 jp2 == 0

let rec jprop_sub sub = function
    | Prop p -> Prop (prop_sub sub p)
    | Joined (p,jp1,jp2) -> Joined (prop_sub sub p, jprop_sub sub jp1, jprop_sub sub jp2)

let rec jprop_fav_add fav = function
  | Prop p -> prop_fav_add fav p
  | Joined (p,jp1,jp2) ->
      prop_fav_add fav p;
      jprop_fav_add fav jp1;
      jprop_fav_add fav jp2

let rec jprop_apply_renaming_no_normalize ren = function
  | Prop p ->
      let p' = prop_apply_renaming_no_normalize ren p
      in Prop p'
  | Joined (p,jp1,jp2) ->
      let p' = prop_apply_renaming_no_normalize ren p in
      let jp1' = jprop_apply_renaming_no_normalize ren jp1 in
      let jp2' = jprop_apply_renaming_no_normalize ren jp2
      in Joined (p',jp1',jp2')

let rec jprop_names_add nset = function
  | Prop p ->
      prop_names_add nset p
  | Joined (p,jp1,jp2) ->
      prop_names_add nset p;
      jprop_names_add nset jp1;
      jprop_names_add nset jp2

let rec jprop_names_update nenv = function
  | Prop p ->
      let p' = prop_names_update nenv p
      in Prop p'
  | Joined (p,jp1,jp2) ->
      let p' = prop_names_update nenv p in
      let jp1' = jprop_names_update nenv jp1 in
      let jp2' = jprop_names_update nenv jp2
      in Joined (p',jp1',jp2')

let jprop_filter (filter: joined_prop -> 'a option) jpl =
  let rec f acc = function
    | [] -> acc
    | (Prop p as jp) :: jpl ->
	(match filter jp with
	  | Some x ->
	      f (x::acc) jpl
	  | None -> f acc jpl)
    | (Joined (p,jp1,jp2) as jp) :: jpl ->
	(match filter jp with
	  | Some x ->
	      f (x::acc) jpl
	  | None ->
	      f acc (jp1::jp2::jpl))
  in f [] jpl

let rec jprop_map (f : prop -> prop) = function
  | Prop p -> Prop (f p)
  | Joined (p,jp1,jp2) -> Joined (f p, jprop_map f jp1, jprop_map f jp2)

let list_reduce name pp f list =
  let rec element_list_reduce acc x = function 
    | [] -> (x, List.rev acc)
    | y::ys -> begin
	E.log "@[<2>.... COMBINE[%s] ....@\n" name;
	E.log "@\nENTRY1: %a@\n" pp x;
	E.log "@\nENTRY2: %a@\n@." pp y;
	match f x y with
        | None -> 
           E.log "@.... COMBINE[%s] FAILED ....@\n@." name;
           element_list_reduce (y::acc) x ys
        | Some x' -> 
           E.log "@[<2>.... COMBINE[%s] SUCCEEDED ....@\n" name;
           E.log "@\nRESULT: %a@\n@." pp x';
           element_list_reduce acc x' ys
      end in
  let rec reduce acc = function
    | [] -> List.rev acc
    | x::xs ->
	let (x',xs') = element_list_reduce [] x xs in 
        reduce (x'::acc) xs' in 
  reduce [] list 

let propset_collapse_impl pset = 
  let f x y =
    if Prover.check_implication x y then Some y
    else if Prover.check_implication y x then Some x
    else None in
  let plist = Propset.propset2proplist pset in
  let plist' = list_reduce "JOIN_IMPL" pp_prop f plist in
  Propset.proplist2propset plist'

let jprop_partial_join mode jp1 jp2 =
  let p1,p2 = jprop_to_prop jp1, jprop_to_prop jp2 in 
  match prop_partial_join_mode mode p1 p2 with
  | None -> None
  | Some p ->
     let p_renamed = prop_rename_primed_footprint_vars p in 
     Some (Joined (p_renamed,jp1,jp2)) 

let jplist_collapse mode jplist =
  let f = jprop_partial_join mode in
  list_reduce "JOIN" pp_jprop_short f jplist

let proplist_collapse_mode mode plist =
  let jplist = List.map (fun p -> Prop p) plist
  in jplist_collapse mode (jplist_collapse mode jplist)

let proplist_collapse_pre = proplist_collapse_mode Pre

let propset_collapse pset =
  let plist = Propset.propset2proplist pset in
  let plist' = proplist_collapse_mode Post plist 
  in Propset.proplist2propset (List.map jprop_to_prop plist')

let join_time = ref 0.0

let propset_join pset1 pset2 =

  let initial_time = Stats.get_current_time () in
  let pset_to_plist pset =
    let f_list acc p = p::acc 
    in Propset.propset_fold f_list [] pset in
  let plist1 = pset_to_plist pset1 in
  let plist2 = pset_to_plist pset2 in
  let rec join_prop_plist plist2_acc p2 = function 
    | [] -> (p2, List.rev plist2_acc)
    | p2'::plist2_rest -> begin
	E.log "@[<2>.... JOIN ....@\n";
	E.log "@\nJOIN SYM HEAP1: %a@\n" pp_prop p2;
	E.log "@\nJOIN SYM HEAP2: %a@\n@." pp_prop p2';
	match prop_partial_join p2 p2' with
	  | None -> 
              E.log "@[.... JOIN FAILED ....@\n@."; 
	      join_prop_plist (p2'::plist2_acc) p2 plist2_rest
	  | Some p2'' -> 
              E.log "@[<2>.... JOIN SUCCEEDED ....@\n";
              E.log "@\nRESULT SYM HEAP: %a@\n@." pp_prop p2''; 
	      join_prop_plist plist2_acc p2'' plist2_rest 
      end in
  let rec join plist1_cur plist2_acc = function
    | [] -> (plist1_cur, plist2_acc)
    | p2::plist2_rest -> 
	let (p2',plist2_rest') = join_prop_plist [] p2 plist2_rest in
	let (p2'',plist1_cur') = join_prop_plist [] p2' plist1_cur 
	in join plist1_cur' (p2''::plist2_acc) plist2_rest' in
  let plist1_res, plist2_res = join plist1 [] plist2 in
  let res = (proplist2propset plist1_res, proplist2propset plist2_res) in

  join_time := !join_time +. (Stats.get_current_time () -. initial_time);
  res

let proplist_meet_generate plist =
  let prop_proplist_meet acc p1 plist2 = 
    let f acc' p2' =
      E.log "@[<2>.... MEET ....@\n";
      E.log "@\nMEET SYM HEAP1: %a@\n" pp_prop p1;
      E.log "@\nMEET SYM HEAP2: %a@\n@." pp_prop p2';
      match prop_partial_meet p1 p2' with
      | None -> 
          E.log "@.... MEET FAILED ....@\n@.";
          acc'
      | Some p' ->
          E.log "@[<2>.... MEET SUCCEEDED ....@\n";
          E.log "@\nRESULT SYM HEAP: %a@\n@." pp_prop p';
          p'::acc' in
    List.fold_left f acc plist2 in

  let rec proplist_self_meet acc plist1 =
    match plist1 with
    | [] -> List.rev acc
    | p1::plist1' -> 
        let acc' = prop_proplist_meet acc p1 plist1' in
        proplist_self_meet acc' plist1' in

  proplist_self_meet [] plist 

let propset_meet_generate pset =
  let plist = Propset.propset2proplist pset in
  let plist_new = proplist_meet_generate plist in
  List.fold_left (fun set p -> 
    let p' = prop_rename_primed_footprint_vars p in 
    Propset.propset_add p' set) pset plist_new

