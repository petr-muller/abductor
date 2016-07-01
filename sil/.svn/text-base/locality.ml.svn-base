(*
 *
 * Copyright (c) 2006-2008,
 *  Cristiano Calcagno    <ccris@doc.ic.ac.uk>
 *  Dino Distefano        <ddino@dcs.qmul.ac.uk>
 *  Peter O'Hearn         <ohearn@dcs.qmul.ac.uk>
 *  Hongseok Yang         <hyang@dcs.qmul.ac.uk>
 * All rights reserved.
 *)

open Cil

module I = Ident
module S = Sil
module P = Prop
module E = Error.MyErr (struct let mode = Error.DEFAULT end)

(* =============== START of the aux_vars object =============== *)    

type aux_vars = 
  { av_param : (I.ident * I.ident) list; 
    av_ret : I.ident;
    mutable av_nparam : (I.ident * I.ident) list; 
    mutable av_size : int }

type aux_vars_tbl = (string, aux_vars) Hashtbl.t

let aux_vars_tbl : aux_vars_tbl = Hashtbl.create 128

let aux_vars_create_param (fd : Cil.fundec) : (I.ident * I.ident) list =
  let create_name postfix = 
    I.string_to_name (fd.svar.vname ^ postfix) in
  let rec get_name_pairs acc index =
    match index with
    | 0 -> acc 
    | n when n > 0 ->  
        let postfix = string_of_int (n-1) in
        let pair = (create_name ("$PreAux" ^ postfix), create_name ("$PreTmpAux" ^ postfix)) in
        get_name_pairs (pair::acc) (n-1) 
    | _ -> assert false in
  let num_of_args = List.length fd.sformals 
    (* 
      (function 
      | TFun (_,Some args,_,_) -> List.length args 
      | TFun (_,None,_,_) -> 0
      | _ -> assert false) fd.svar.vtype 
     *)
  in
  let names_of_formals = 
    get_name_pairs [] num_of_args in
  let id_pairs_of_formals = 
    List.map (fun (cut_name,temp_name) -> 
      I.create_fresh_normal_ident cut_name, I.create_fresh_normal_ident temp_name) 
      names_of_formals in 
  id_pairs_of_formals

let aux_vars_create_nparam (id_acc : (I.ident * I.ident) list) 
    (fd : Cil.fundec) (n : int) : (I.ident * I.ident) list =
  if n < 0 then assert false
  else 
    let pname = fd.svar.vname in
    let base_name =  I.string_to_name (pname ^ "$Cut")  in
    let base_tmp_name = I.string_to_name (pname ^ "$CutTmp") in
    let rec f acc i = 
      if i <= 0 then acc 
      else 
	let fresh_id = I.create_fresh_normal_ident base_name in
	let fresh_tmp_id = I.create_fresh_normal_ident base_tmp_name
	in f ((fresh_id,fresh_tmp_id)::acc) (i-1) 
    in f id_acc n 

let aux_vars_create_ret (fd : Cil.fundec) : I.ident =
  let pname = fd.svar.vname in
  let ret_name = I.string_to_name (pname ^ "$AuxRet") in
  let ret_id = I.create_fresh_normal_ident ret_name
  in ret_id

let aux_vars_get_param (fd : Cil.fundec) : (I.ident * I.ident) list =
  let pname = fd.svar.vname in
  try
    let aux = Hashtbl.find aux_vars_tbl pname
    in aux.av_param
  with Not_found -> 
    let ids_param = aux_vars_create_param fd in
    let id_ret = aux_vars_create_ret fd in
    let aux = { av_param=ids_param; av_ret=id_ret; av_nparam=[]; av_size=0 }
    in 
      Hashtbl.add aux_vars_tbl pname aux;
      ids_param

let aux_vars_get_nparam (fd : Cil.fundec) 
    (n : int) : (I.ident * I.ident) list =
  let _ = if n < 0 then assert false else () in
  let pname = fd.svar.vname 
  in
  let f_exist_sufficient aux size =
    let id_pairs = aux.av_nparam in
    let m = size - n in
    let rec remove_first_n_elements k l = 
      if k = 0 then l else 
	try
	  remove_first_n_elements (k-1) (List.tl l)
	with Invalid_argument _ -> 
	  assert false in
    let id_pairs' = remove_first_n_elements m id_pairs
    in List.rev id_pairs'
  in 
  let f_exist_notsufficient aux size =
    begin
      aux.av_size <- n;
      aux.av_nparam <- aux_vars_create_nparam aux.av_nparam fd (n-size);
      List.rev aux.av_nparam
    end 
  in 
  let f_notexist _ = 
    let ids_param = aux_vars_create_param fd in
    let ids_nparam = aux_vars_create_nparam [] fd n in
    let id_ret = aux_vars_create_ret fd in
    let aux_vars = 
      { av_param=ids_param;
	av_ret = id_ret;
	av_nparam=ids_nparam;
	av_size=n }
    in begin
      Hashtbl.add aux_vars_tbl pname aux_vars;
      List.rev ids_nparam
    end
  in 
    try 
      let aux = Hashtbl.find aux_vars_tbl pname in
      let size = aux.av_size 
      in 
	if size >= n then f_exist_sufficient aux size
	else f_exist_notsufficient aux size
    with Not_found -> 
      f_notexist ()


let aux_vars_get_ret (fd : Cil.fundec) : I.ident =
  let pname = fd.svar.vname
  in 
    try
      let aux = Hashtbl.find aux_vars_tbl pname
      in aux.av_ret
    with Not_found -> begin
      let ids_param = aux_vars_create_param fd in
      let id_ret = aux_vars_create_ret fd in
      let aux = { av_param=ids_param; av_ret=id_ret; av_nparam=[]; av_size=0 }
      in 
	Hashtbl.add aux_vars_tbl pname aux;
	id_ret
    end  
  
(* =============== END of the aux_vars object =============== *) 





(* =============== START of compute_reachable =============== *)

module ExpSet = 
  Set.Make(struct
    type t = S.exp
    let compare = S.exp_compare
  end)

let explist_to_expset base_eset elist =
  List.fold_left (fun eset e -> ExpSet.add e eset) base_eset elist

let sigma_annotate sigma = 
  let rec get_tgts acc = function
    | S.Eexp e -> (S.root_of_lexp e)::acc
    | S.Estruct fld_se_list ->
	List.fold_left (fun acc' (_,se') -> get_tgts acc' se') acc fld_se_list
    | S.Earray (_, idx_se_list) -> 
	List.fold_left (fun acc' (_,se') -> get_tgts acc' se') acc idx_se_list in
  let annotate hpred = 
    match hpred with
      | S.Hpointsto (root, next_se, _) -> 
	  let tgts = get_tgts [] next_se 
	  in ([root], tgts, hpred) 
      | S.Hlseg (_, _, root, next, back_es) -> 
	  let tgts = next::back_es 
	  in ([root], tgts, hpred) 
      | S.Hdllseg (_, _, iF,oF,oB,iB, back_es) -> 
	  let tgts = iF::oF::oB::iB::back_es 
	  in ([iF;iB], tgts, hpred) 
  in List.map annotate sigma

let sigma_unannotate sigma_ann =
  List.map (fun (_,_,hpred) -> hpred) sigma_ann

let compute_cutpoints_info callee cutpoints = 
  let n = List.length cutpoints in
  let cut_id_pairs = aux_vars_get_nparam callee n in
  let f (cut_id,temp_id) e = (cut_id, temp_id, e)
  in try
      List.map2 f cut_id_pairs cutpoints
    with Invalid_argument _ -> assert false

let sigma_split callee entries sigma_in =
  let sigma_ann_in = sigma_annotate sigma_in in
  let marked = ref entries in
  let reach_done = ref [] 
  in
  let rec f_mem = function 
    | [] -> false
    | e::es -> (ExpSet.mem e !marked) || (f_mem es) 
  in
  let rec f_split reach sigma_ann_unreach = function
    | [] -> 
	if reach = [] then sigma_ann_unreach
	else begin
	  reach_done := reach::!reach_done;
	  f_split [] [] sigma_ann_unreach
	end
    | (srcs,tgts,hpred) as hpred_ann :: sigma_ann ->
        if not (f_mem srcs) then
          f_split reach (hpred_ann::sigma_ann_unreach) sigma_ann
	else begin
          marked := explist_to_expset !marked tgts;
	  f_split (hpred::reach) sigma_ann_unreach sigma_ann 
	end 
  in
  let f_cutpoints1 _ = 
    let rec filter = function
      | S.Var id -> I.ident_is_normal id
      | _ -> false
    in ExpSet.filter filter !marked
  in
  let rec f_cutpoints2 cset_acc = function
    | [] -> 
	let clist = ExpSet.elements (ExpSet.diff cset_acc entries) in
	let rec filter = function
	  | S.Var _ | S.Lfield _ -> true
	  | S.Const_int _ | S.Const_fun _ | S.UnOp _ | S.BinOp _ | S.Lvar _ | S.Lindex _ | S.Sizeof _ -> false
	  | S.Cast (_,e) -> filter e in
	let clist' = List.filter filter clist 
	in List.sort S.exp_compare clist' 
    | (_,tgts,hpred)::sigma_ann -> 
	let cuts = List.filter (fun e -> ExpSet.mem e !marked) tgts in 
	let cset_acc' = List.fold_left (fun cset e -> ExpSet.add e cset) cset_acc cuts
	in f_cutpoints2 cset_acc' sigma_ann 
  in 
  let (cutpoints_info, sigma_reach, sigma_unreach) = 
    let sigma_ann_unreach = f_split [] [] sigma_ann_in in
    let cutpoints = f_cutpoints1 () in
    let cutpoints' = f_cutpoints2 cutpoints sigma_ann_unreach in 
    let cutpoints_info = compute_cutpoints_info callee cutpoints'
    in (cutpoints_info, List.flatten !reach_done, sigma_unannotate sigma_ann_unreach) 
  in 
    (cutpoints_info, sigma_unreach, sigma_reach)
  
let compute_reachable (callee:Cil.fundec) (globals:S.pvar list) (nparams:S.exp list) 
      (p:P.prop) : (I.ident * I.ident * S.exp) list * P.prop * P.prop =
  let entry_list = 
    List.fold_left (fun acc pv -> (S.Lvar pv)::acc) nparams globals in
  let entries = 
    explist_to_expset ExpSet.empty entry_list in
  let sigma = P.prop_get_sigma p in
  let (cutpoints_info, sigma_unreach, sigma_reach) = sigma_split callee entries sigma in
  let p_unreach = P.prop_replace_sigma sigma_unreach p in
  let p_reach = P.prop_replace_sigma sigma_reach p in 
  (cutpoints_info, p_unreach, p_reach)


(* splits a proposition into the unreachable part from params and
 * the reachable part. Cannot handle recursive calls. *)
let split (callee:Cil.fundec) (globals: S.pvar list) (params:S.exp list) 
  (p:P.prop) : (I.ident * I.ident * S.exp) list * P.prop * P.prop =
  let nparams = List.map (fun e -> S.root_of_lexp (P.exp_normalize_prop p e)) params  
  in 
    if !Config.locality_level = 0 then 
      ([], P.prop_emp, p)
    else if !Config.locality_level = 1 then
      let (cutpoints_info, p_unreach,p_reach) = compute_reachable callee globals nparams p 
      in 
	E.log "@[<2>.... Split a Prop for Call to %s....@\n" (callee.svar.vname);
	E.log "In: %a@\n@\n" P.pp_prop p;
	E.log "Unreach: %a@\n@\n" P.pp_prop p_unreach;
	E.log "Reach: %a@\n@." P.pp_prop p_reach;
	(cutpoints_info, p_unreach, p_reach)
    else
      assert false

(* =============== END of split =============== *)






(* =============== START of combine =============== *)

(* combine two propositions. Currently, drop all equalities from the
 * second argument. *)
let combine (callee: Cil.fundec) frame_p p =
  let p_res =  
    if !Config.locality_level = 0 then 
      p
    else if !Config.locality_level = 1 then
      let (eqs,sigma) =
	let p_renamed = P.prop_rename_primed_fresh p in 
	let sigma = P.prop_get_sigma p_renamed in
	let eqs = P.prop_get_equalities p_renamed 
	in (eqs, sigma) in
      let p_combined = 
	let frame_p' = P.prop_sigma_star frame_p sigma 
        in List.fold_left (fun p (e1,e2) -> P.conjoin_eq e1 e2 p) frame_p' eqs 
      in p_combined
    else 
      assert false
  in 
    E.log "@[<2>.... Combine Props at the end of %s ....@\n" callee.svar.vname;
    E.log "Frame: %a@\n@\n" P.pp_prop frame_p;
    E.log "Non-Frame: %a@\n@\n" P.pp_prop p;
    E.log "Combined: %a@\n@." P.pp_prop p_res;
    Some p_res

(* =============== END of combine =============== *)
