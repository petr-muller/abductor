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
open Prop
module F = Format
module Exn = Exceptions

module E = Error.MyErr (struct let mode = Error.DEFAULT end)
(*let () = E.set_mode Error.ALWAYS
let () = E.set_colour Error.green*)




(** {2 Theorem Proving} *)

(** Check [prop |- e1=e2]. *)
let check_equal prop e1 e2 = 
  let pi = prop_get_pi prop in
  let n_e1 = exp_normalize_prop prop e1 in
  let n_e2 = exp_normalize_prop prop e2 
  in if (exp_compare n_e1 n_e2 = 0) then true
    else 
      let eq = Aeq(n_e1,n_e2) in
      let n_eq = atom_normalize_prop prop eq 
      in List.exists (atom_equal n_eq) pi

(** [is_root prop base_exp exp] checks whether [base_exp =
    exp.offlist] for some list of offsets [offlist]. If so, it returns
    [Some(offlist)].  Otherwise, it returns [None]. Assumes that
    [base_exp] points to the beginning of a structure, not the middle.
*)
let is_root prop base_exp exp = 
  let rec f offlist_past e = match e with
    | Var _ | Const_int _ | Const_fun _ | UnOp _ | BinOp _ | Lvar _ | Sizeof _ -> 
	if (check_equal prop base_exp e)
	then Some(offlist_past)
	else None
    | Cast(t,sub_exp) -> f offlist_past sub_exp
    | Lfield(sub_exp,fldname) -> f (Off_fld(fldname)::offlist_past) sub_exp
    | Lindex(sub_exp,e) -> f (Off_index(e)::offlist_past) sub_exp
  in f [] exp


(** Check whether [prop |- e1!=e2]. *)
let check_disequal prop e1 e2 =
  let pi = prop_get_pi prop in
  let spatial_part = prop_get_sigma prop in
  let n_e1 = exp_normalize_prop prop e1 in
  let n_e2 = exp_normalize_prop prop e2 in
  let does_pi_imply_disequal ne ne' = 
    let diseq = Aneq(ne,ne') in
    let n_diseq = atom_normalize_prop prop diseq in 
    List.exists (atom_equal n_diseq) pi in  
  let neq_spatial_part _ =
    let rec f sigma_irrelevant e = function
      | [] -> None
      | Hpointsto (base, _, _) as hpred :: sigma_rest -> 
          (match is_root prop base e with 
           | None -> 
               let sigma_irrelevant' = hpred :: sigma_irrelevant
  	       in f sigma_irrelevant' e sigma_rest
  	   | Some _ -> 
               let sigma_irrelevant' = (List.rev sigma_irrelevant) @ sigma_rest 
	       in Some (true, sigma_irrelevant'))
      | Hlseg (k,_, e1, e2, _) as hpred :: sigma_rest -> 
          (match is_root prop e1 e with
	   | None ->
               let sigma_irrelevant' = hpred :: sigma_irrelevant
	       in f sigma_irrelevant' e sigma_rest
	   | Some _ ->
               if (k==Lseg_NE || does_pi_imply_disequal e1 e2) then
	         let sigma_irrelevant' = (List.rev sigma_irrelevant) @ sigma_rest
		 in Some (true, sigma_irrelevant')
	       else if (exp_equal e2 (Const_int 0)) then
		 let sigma_irrelevant' = (List.rev sigma_irrelevant) @ sigma_rest
                 in Some (false, sigma_irrelevant') 
	       else 
		 let sigma_rest' = (List.rev sigma_irrelevant) @ sigma_rest 
		 in f [] e2 sigma_rest') 
      | Hdllseg (Lseg_NE,_, iF,oB,oF,iB, _) :: sigma_rest ->
         if is_root prop iF e != None || is_root prop iB e != None then
           let sigma_irrelevant' = (List.rev sigma_irrelevant) @ sigma_rest
  	   in Some (true, sigma_irrelevant')
	 else
	   let sigma_irrelevant' = (List.rev sigma_irrelevant) @ sigma_rest
           in Some (false, sigma_irrelevant')
      | Hdllseg (Lseg_PE,_,iF,oB,oF,iB,_) as hpred :: sigma_rest -> 
          (match is_root prop iF e with
	  | None -> 
	      let sigma_irrelevant' = hpred :: sigma_irrelevant
	      in f sigma_irrelevant' e sigma_rest
	  | Some _ ->
	      if (does_pi_imply_disequal iF oF) then
	        let sigma_irrelevant' = (List.rev sigma_irrelevant) @ sigma_rest
		in Some (true, sigma_irrelevant')
	      else if (exp_equal oF (Const_int 0)) then
	        let sigma_irrelevant' = (List.rev sigma_irrelevant) @ sigma_rest
	        in Some (false, sigma_irrelevant') 
              else 
	        let sigma_rest' = (List.rev sigma_irrelevant) @ sigma_rest 
		in f [] oF sigma_rest')
    in
    let f_null_check sigma_irrelevant e sigma_rest =
      if not (exp_equal e (Const_int 0)) then f sigma_irrelevant e sigma_rest
      else 
  	let sigma_irrelevant' = (List.rev sigma_irrelevant) @ sigma_rest
	in Some (false, sigma_irrelevant') 
    in match f_null_check [] n_e1 spatial_part with
      | None -> false 
      | Some (e1_allocated, spatial_part_leftover) -> 
          (match f_null_check [] n_e2 spatial_part_leftover with
          | None -> false
          | Some ((e2_allocated : bool), _) -> e1_allocated || e2_allocated) in
  let neq_pure_part () = 
    does_pi_imply_disequal n_e1 n_e2
  in (neq_pure_part ()) || (neq_spatial_part ())

(** Check whether [prop |- allocated(e)]. *)
let check_allocatedness prop e =
  let n_e = exp_normalize_prop prop e in
  let spatial_part = prop_get_sigma prop in
  let f = function
    | Hpointsto (base, _, _) -> 
        is_root prop base n_e != None
    | Hlseg (k,_,e1,e2,_) ->
	if k==Lseg_NE || check_disequal prop e1 e2 then 
          is_root prop e1 n_e != None
	else false
    | Hdllseg (k,_,iF,oB,oF,iB,_) -> 
	if k==Lseg_NE || check_disequal prop iF oF || check_disequal prop iB oB then 
          is_root prop iF n_e != None || is_root prop iB n_e != None
	else false
  in List.exists f spatial_part  

(** Inconsistency checking ignoring footprint. *)
let check_inconsistency_base prop =
  let pi = prop_get_pi prop in
  let inconsistent_ptsto _ =
    check_allocatedness prop (Const_int 0) in
  let inconsistent_two_hpreds _ =
    let rec f e sigma_seen = function
      | [] -> false
      | (Hpointsto (e1,_,_) as hpred) :: sigma_rest
      | (Hlseg (Lseg_NE,_,e1,_,_) as hpred) :: sigma_rest ->
          if exp_equal e1 e then true
	  else f e (hpred::sigma_seen) sigma_rest
      | (Hdllseg (Lseg_NE,_,iF,_,_,iB,_) as hpred) :: sigma_rest ->
          if exp_equal iF e || exp_equal iB e then true
	  else f e (hpred::sigma_seen) sigma_rest
      | Hlseg (Lseg_PE,_,e1,Const_int 0,_) as hpred :: sigma_rest -> 
          if exp_equal e1 e then true
	  else f e (hpred::sigma_seen) sigma_rest
      | Hlseg (Lseg_PE,_,e1, e2,_) as hpred :: sigma_rest -> 
          if exp_equal e1 e 
          then
	    let prop' = prop_of_sigma (sigma_seen@sigma_rest) in
	    let prop_new = conjoin_eq e1 e2 prop' in
	    let sigma_new = prop_get_sigma prop_new in
	    let e_new = exp_normalize_prop prop_new e 
	    in f e_new [] sigma_new
	  else f e (hpred::sigma_seen) sigma_rest
      | Hdllseg (Lseg_PE,_,e1,e2,Const_int 0,_,_) as hpred :: sigma_rest -> 
          if exp_equal e1 e then true
	  else f e (hpred::sigma_seen) sigma_rest
      | Hdllseg (Lseg_PE,_,e1,e2,e3,e4,_) as hpred :: sigma_rest -> (* ddino: double check this *)
          if exp_equal e1 e 
          then
	    let prop' = prop_of_sigma (sigma_seen@sigma_rest) in
	    let prop_new = conjoin_eq e1 e3 prop' in
	    let sigma_new = prop_get_sigma prop_new in
	    let e_new = exp_normalize_prop prop_new e 
	    in f e_new [] sigma_new
	  else f e (hpred::sigma_seen) sigma_rest
    in
    let rec check sigma_seen = function
      | [] -> false
      | (Hpointsto (e1,_,_) as hpred) :: sigma_rest
      | (Hlseg (Lseg_NE,_,e1,_,_) as hpred) :: sigma_rest ->
	  if (f e1 [] (sigma_seen@sigma_rest)) then true
	  else check (hpred::sigma_seen) sigma_rest
      | Hdllseg (Lseg_NE,_,iF,_,_,iB,_) as hpred :: sigma_rest ->
	  if f iF [] (sigma_seen@sigma_rest) || f iB [] (sigma_seen@sigma_rest)  then true
	  else check (hpred::sigma_seen) sigma_rest
      | (Hlseg (Lseg_PE,_,_,_,_) as hpred) :: sigma_rest
      | (Hdllseg (Lseg_PE,_,_,_,_,_,_) as hpred) :: sigma_rest ->
	  check (hpred::sigma_seen) sigma_rest
    in
    let sigma = prop_get_sigma prop 
    in check [] sigma in
  let inconsistent_atom = function
    | Aeq (e1,e2) -> (match e1,e2 with
	| Const_int n, Const_int m -> n<>m
	| _ -> false)
    | Aneq (e1,e2) -> (match e1,e2 with
	| Const_int n, Const_int m -> n=m
	| _ -> (exp_compare e1 e2 = 0))
  in inconsistent_ptsto () || inconsistent_two_hpreds () || List.exists inconsistent_atom pi

(** Inconsistency checking. *)
let check_inconsistency prop =
 (* ddino: in a previous implementation I was raising the exception 
    as soon as the footprint was inconsistent. However, this would cause some
    false alarm given by the pure part being inconsistent. But I notice that 
    also the pure part of the prop would be inconsistent (Is this true always? if yes it's good
    else we might miss some errors). So to avoid these false alarm I first give priority to
    the inconsistency of prop. The exception is risen only if prop is consistent to catch the fact
    the the inconsistency of footprint should come from starring twice the same cell.
    But if this will imply we miss some possible errors then better to go back to the old
    versiong when we check first for the consistency of footprint. In any case I notice that
    in that case it doesn't give many false alarm (eg. for firewire only 2).
 *)
  match check_inconsistency_base prop, check_inconsistency_base (prop_extract_footprint prop) with 
  | true, _ -> true 
  | false,true -> raise (Exn.Possible_memory_fault prop)
  | false, false -> false
(*  check_inconsistency_base prop || check_inconsistency_base (prop_extract_footprint prop)*)

let atom_mem a l =
  List.exists (fun a' -> atom_equal a a') l

type subst2 = subst*subst

type exc_body =
    | EXC_FALSE
    | EXC_FALSE_HPRED of hpred
    | EXC_FALSE_EXPS of exp * exp
    | EXC_FALSE_SEXPS of strexp * strexp
    | EXC_FALSE_ATOM of atom
    | EXC_FALSE_SIGMA of hpred list

exception IMPL_EXC of string * subst2 * exc_body

exception MISSING_EXC of string

let missing_pi = ref []
let missing_sigma = ref []
let frame_fld = ref []
let missing_fld = ref []

let _d_missing sub =
  E.d_str "SUB: "; Prop.d_sub sub;
  if !missing_pi != [] && !missing_sigma != []
  then (Prop.d_pi !missing_pi; E.d_str "*"; Prop.d_sigma !missing_sigma)
  else if !missing_pi != []
  then Prop.d_pi !missing_pi
  else if !missing_sigma != []
  then Prop.d_sigma !missing_sigma;
  if !missing_fld != []
  then E.d_str "MISSING FLD: "; Prop.d_sigma !missing_fld

let d_missing indent sub =
  if !missing_pi != [] || !missing_sigma!=[] || !missing_fld != [] then
    (E.d_indent indent;
     E.d_str "[";
     _d_missing sub;
     E.d_strln "]")

let d_frame_fld () =
  if !frame_fld != []
  then (E.d_str "[FRAME FLD: "; Prop.d_sigma !frame_fld; E.d_str "]")

(** Dump an implication *)
let d_implication indent (sub1,sub2) (p1,p2) =
  let p1,p2 = prop_sub sub1 p1, prop_sub sub2 p2
  in
    E.d_indent indent;
    E.d_str "SUB:"; Prop.d_sub sub1; E.d_ln ();
    E.d_indent indent;
    Prop.d_prop p1; E.d_ln ();
    d_missing indent sub2;
    E.d_indent indent; E.d_strln "|-";
    E.d_indent indent;
    Prop.d_prop p2;
    d_frame_fld ();
    E.d_ln ()

let implication_lhs = ref prop_emp
let implication_rhs = ref prop_emp

let d_implication_error (s,subs,body) =
  let p1,p2 = !implication_lhs,!implication_rhs in
  let d_inner () = match body with
    | EXC_FALSE ->
	()
    | EXC_FALSE_HPRED hpred ->
	E.d_str "on ";
	Sil.d_hpred hpred;
    | EXC_FALSE_EXPS (e1,e2) ->
	E.d_str "on ";
	Sil.d_exp e1; E.d_str ","; Sil.d_exp e2;
    | EXC_FALSE_SEXPS (se1,se2) ->
	E.d_str "on ";
	Sil.d_sexp se1; E.d_str ","; Sil.d_sexp se2;
    | EXC_FALSE_ATOM a ->
	E.d_str "on ";
	Sil.d_atom a;
    | EXC_FALSE_SIGMA sigma ->
	E.d_str "on ";
	Prop.d_sigma sigma;
  in
	E.d_strln "$$$$$$$ Implication";
	d_implication 0 subs (p1,p2);
	E.d_strln ("$$$$$$ error: " ^ s);
	d_inner ();
	E.d_strln " returning FALSE"

(** Extend [sub1] and [sub2] to witnesses that each instance of
    [e1[sub1]] is an instance of [e2[sub2]]. Raise IMP_FALSE if not
    possible. *)
let rec exp_imply calc_missing subs e1_in e2_in : subst2 =
  let e1,e2 = exp_sub (fst subs) e1_in, exp_sub (snd subs) e2_in in
  let var_imply v1 v2 : subst2 = 
    match ident_is_primed v1, ident_is_primed v2 with
      | false,false ->
	  if ident_equal v1 v2 then subs
	  else if calc_missing && ident_is_footprint v1 && ident_is_footprint v2
	  then
	    let () = missing_pi := Aeq (e1_in,e2_in) :: !missing_pi
	    in subs
	  else raise (IMPL_EXC ("exps",subs,(EXC_FALSE_EXPS (e1,e2))))
      | true,false -> raise (IMPL_EXC ("exps",subs,(EXC_FALSE_EXPS (e1,e2))))
      | false,true ->
	  let sub2' = sub_join (snd subs) (sub_of_list [v2, e1])
	  in (fst subs,sub2')		  
      | true,true ->
	  let v1' = Ident.create_fresh_normal_ident (ident_name v1) in
	  let sub1' = sub_join (fst subs) (sub_of_list [v1, Var v1']) in
	  let sub2' = sub_join (snd subs) (sub_of_list [v2, Var v1'])
	  in (sub1',sub2')  in

    match e1,e2 with
      | Var v1, Var v2 ->
	  var_imply v1 v2
      | e1, Var v2 ->
	  if ident_is_primed v2 then
	    let sub2' = sub_join (snd subs) (sub_of_list [v2, e1])
	    in (fst subs,sub2')
	  else raise (IMPL_EXC ("expressions not equal",subs,(EXC_FALSE_EXPS (e1,e2))))
      | Var v1, e2 ->
	  if calc_missing then
	    let () = missing_pi := Aeq (e1_in,e2_in) :: !missing_pi
	    in subs
	  else raise (IMPL_EXC ("expressions not equal",subs,(EXC_FALSE_EXPS (e1,e2))))
      | Lvar v1, Lvar v2 ->
	  if pvar_equal v1 v2 then subs
	  else raise (IMPL_EXC ("expressions not equal",subs,(EXC_FALSE_EXPS (e1,e2))))
      | Const_int n, Const_int m ->
	  if n<>m then raise (IMPL_EXC ("constants not equal",subs,(EXC_FALSE_EXPS (e1,e2))))
	  else subs
      | e1, Const_int m ->
	  raise (IMPL_EXC ("lhs not constant",subs,(EXC_FALSE_EXPS (e1,e2))))
      | BinOp(op1,e1,f1), BinOp(op2,e2,f2) when op1==op2 ->
	  exp_imply calc_missing (exp_imply calc_missing subs e1 e2) f1 f2
      | Lfield(e1,fd1), Lfield(e2,fd2) when fd1==fd2 ->
	  exp_imply calc_missing subs e1 e2
      | Lindex(e1,f1),Lindex(e2,f2) ->
	  exp_imply calc_missing (exp_imply calc_missing subs e1 e2) f1 f2	
      | _ ->
	  d_implication_error ("exp_imply not implemented",subs,(EXC_FALSE_EXPS (e1,e2)));
	  raise Exn.Abduction_Case_Not_implemented

(** Convert a path (from lhs of a |-> to a field name present only in
    the rhs) into an id. If the lhs was a footprint var, the id is a
    new footprint var. Othewise it is a var wiht the path in the name
    and stamp -1 *)
let path_to_id path =
  let rec f = function
    | Var id ->
	if ident_is_footprint id then None
	else Some (name_to_string (ident_name id) ^ (string_of_int (ident_get_stamp id)))
    | Lfield (e,fld) ->
	(match f e with
	  | None -> None
	  | Some s -> Some (s ^ "_" ^ (name_to_string fld)))
    | Lindex (e,e') ->
	None
    | _ -> None
  in
    if !Config.footprint then Ident.create_fresh_footprint_ident name_siltmp
    else match f path with
      | None -> Ident.create_fresh_footprint_ident name_siltmp
      | Some s -> Ident.create_normal_ident (string_to_name s) (-1)

(** Extend [sub1] and [sub2] to witnesses that each instance of
    [se1[sub1]] is an instance of [se2[sub2]]. Raise IMP_FALSE if not
    possible. *)
let rec strexp_imply source calc_missing subs se1 se2 : subst2 * (strexp option) * (strexp option) = match se1,se2 with
  | Eexp e1, Eexp e2 ->
      (exp_imply calc_missing subs e1 e2,None,None)
  | Estruct fsel1, Estruct fsel2 ->
      let subs',fld_frame,fld_missing = struct_imply source calc_missing subs fsel1 fsel2 in
      let fld_frame_opt = if fld_frame != [] then Some (Estruct fld_frame) else None in
      let fld_missing_opt = if fld_missing != [] then Some (Estruct fld_missing) else None
      in subs',fld_frame_opt,fld_missing_opt
  | Estruct _, Eexp e2 ->
      (let e2' = exp_sub (snd subs) e2 in match e2' with
	| Var id2 when ident_is_primed id2 ->
	    let id2' = Ident.create_fresh_normal_ident (ident_name id2) in
	    let sub2' = sub_join (snd subs) (sub_of_list [id2, Var id2'])
	    in (fst subs,sub2'),None,None
	| _ ->
	    d_implication_error ("sexp_imply not implemented",subs,(EXC_FALSE_SEXPS (se1,se2)));
	    raise Exn.Abduction_Case_Not_implemented)
  | Earray _, Earray _ ->
      if strexp_equal se1 se2
      then subs,None,None
      else
	(d_implication_error ("sexp_imply not implemented",subs,(EXC_FALSE_SEXPS (se1,se2)));
	 raise Exn.Abduction_Case_Not_implemented)
  | Eexp _, Estruct fsel ->
      d_implication_error ("WARNING: function call with parameters of struct type, treating as unknown",subs,(EXC_FALSE_SEXPS (se1,se2)));
      let fsel' =
	let f (f,se) =
	  (f,Eexp (Var (create_fresh_normal_ident name_siltmp)))
	in List.map f fsel
      in strexp_imply source calc_missing subs (Estruct fsel') se2
  | _ ->
      d_implication_error ("sexp_imply not implemented",subs,(EXC_FALSE_SEXPS (se1,se2)));
      raise Exn.Abduction_Case_Not_implemented

and struct_imply source calc_missing subs fsel1 fsel2 : subst2 * ((name*strexp) list) * ((name*strexp) list) = match fsel1,fsel2 with
  | _, [] -> subs,fsel1,[]
  | (f1,se1)::fsel1', (f2,se2)::fsel2' ->
      (match name_compare f1 f2 with
	| 0 ->
	    let subs',se_frame,se_missing = strexp_imply (Lfield (source,f2)) calc_missing subs se1 se2 in
	    let subs'',fld_frame,fld_missing = struct_imply source calc_missing subs' fsel1' fsel2' in
	    let fld_frame' = match se_frame with
	      | None -> fld_frame
	      | Some se -> (f1,se)::fld_frame in
	    let fld_missing' = match se_missing with
	      | None -> fld_missing
	      | Some se -> (f1,se)::fld_missing
	    in subs'',fld_frame',fld_missing'
	| n when n<0 ->
	    let subs',fld_frame,fld_missing = struct_imply source calc_missing subs fsel1' fsel2
	    in subs',((f1,se1)::fld_frame),fld_missing
	| _ ->
	    let subs' = strexp_imply_nolhs (Lfield (source,f2)) calc_missing subs se2 in
	    let subs',fld_frame,fld_missing = struct_imply source calc_missing subs' fsel1 fsel2' in
	    let fld_missing' = (f2,se2)::fld_missing
	    in subs',fld_frame,fld_missing'
      )
  | [],(f2,se2)::fsel2' ->
      let subs' = strexp_imply_nolhs (Lfield (source,f2)) calc_missing subs se2 in
      let subs'',fld_frame,fld_missing = struct_imply source calc_missing subs' [] fsel2'
      in subs'',fld_frame,(f2,se2)::fld_missing

and array_imply source calc_missing subs esel1 esel2 = match esel1,esel2 with
  | _,[] -> subs
  | (e1,se1)::esel1', (e2,se2)::esel2' ->
      (match exp_compare e1 e2 with
	| 0 ->
	    let subs',_,_ = strexp_imply (Lindex (source,e1)) calc_missing subs se1 se2
	    in array_imply source calc_missing subs' esel1' esel2'
	| n when n<0 -> array_imply source calc_missing subs esel1' esel2
	| _ ->
	    let subs' = strexp_imply_nolhs (Lindex (source,e2)) calc_missing subs se2
	    in array_imply source calc_missing subs' esel1 esel2'
      )
  | [], (e2,se2)::esel2' ->
      let subs' = strexp_imply_nolhs (Lindex (source,e2)) calc_missing subs se2
      in array_imply source calc_missing subs' [] esel2'

and strexp_imply_nolhs source calc_missing subs se2 = match se2 with
  | Eexp _e2 ->
      let e2 = exp_sub (snd subs) _e2 in
	(match e2 with
	  | Var v2 when ident_is_primed v2 ->
	      let v2' = path_to_id source in
	      let sub2' = sub_join (snd subs) (sub_of_list [v2, Var v2'])
	      in (fst subs,sub2')
	  | Var _ ->
	      if calc_missing then subs
	      else raise (IMPL_EXC ("exp only in rhs is not a primed var",subs,EXC_FALSE))
	  | Const_int n when calc_missing ->
	      let id = path_to_id source in
	      let () = missing_pi := Aeq (Var id,_e2) :: !missing_pi
	      in subs
	  | _ ->
	      raise (IMPL_EXC ("exp only in rhs is not a primed var",subs,EXC_FALSE)))
  | Estruct fsel2 ->
      (fun (x,y,z) -> x) (struct_imply source calc_missing subs [] fsel2)
  | Earray (_,esel2) ->
      array_imply source calc_missing subs [] esel2

let rec exp_list_imply calc_missing subs l1 l2 = match l1,l2 with
  | [],[] -> subs
  | e1::l1,e2::l2 ->
      exp_list_imply calc_missing (exp_imply calc_missing subs e1 e2) l1 l2
  | _ -> assert false

let filter_ptsto_lhs sub e0 = function
  | Hpointsto (e,_,_) -> if exp_equal e0 (exp_sub sub e) then Some () else None
  | _ -> None

let filter_ne_lhs sub e0 = function
  | Hpointsto (e,_,_) -> if exp_equal e0 (exp_sub sub e) then Some () else None
  | Hlseg (Lseg_NE,_,e,_,_) -> if exp_equal e0 (exp_sub sub e) then Some () else None
  | Hdllseg (Lseg_NE,_,e,_,_,e',_) -> 
      if exp_equal e0 (exp_sub sub e) || exp_equal e0 (exp_sub sub e') 
      then Some ()
      else None
  | _ -> None


let filter_hpred sub hpred2 hpred1 = match (hpred_sub sub hpred1),hpred2 with
  | Hlseg(Lseg_NE,hpara1,e1,f1,el1),Hlseg(Lseg_PE,hpara2,e2,f2,el2) ->
      if hpred_equal (Hlseg(Lseg_PE,hpara1,e1,f1,el1)) hpred2 then Some false else None
  | Hlseg(Lseg_PE,hpara1,e1,f1,el1),Hlseg(Lseg_NE,hpara2,e2,f2,el2) ->
      if hpred_equal (Hlseg(Lseg_NE,hpara1,e1,f1,el1)) hpred2 then Some true else None (* return missing disequality *)
  | Hpointsto(e1,se1,te1),Hlseg(k,hpara2,e2,f2,el2) ->
      if exp_equal e1 e2 then Some false else None
  | hpred1,hpred2 -> if hpred_equal hpred1 hpred2 then Some false else None

let prop_sub sub prop =
  let pi = pi_sub sub (prop_get_pi prop) in
  let sigma = sigma_sub sub (prop_get_sigma prop)
  in prop_replace_sigma sigma (prop_replace_pi pi prop)

let hpred_has_primed_lhs sub hpred =
  let exp_is_primed e =
    fav_exists (exp_fav (exp_sub sub e)) ident_is_primed
  in match hpred with
    | Hpointsto (e,_,_) ->
	exp_is_primed e
    | Hlseg (_,_,e,_,_) ->
	exp_is_primed e
    | Hdllseg (_,_,iF,oB,oF,iB,_) ->
	exp_is_primed iF && exp_is_primed iB

let move_primed_lhs_from_front subs sigma = match sigma with
  | [] -> sigma
  | hpred::sigma' ->
      if hpred_has_primed_lhs (snd subs) hpred then
	let (sigma_primed,sigma_unprimed) = List.partition (hpred_has_primed_lhs (snd subs)) sigma
	in match sigma_unprimed with
	  | [] -> raise (IMPL_EXC ("on rhs all lhs's are primed",subs,(EXC_FALSE_SIGMA sigma)))
	  | _::_ -> sigma_unprimed @ sigma_primed
      else sigma

let name_n = string_to_name "n"

let rec hpred_imply nesting calc_missing subs prop1 hpred2 : subst2*prop = match hpred2 with
  | Hpointsto (_e2,se2,t) ->
      let e2 = exp_sub (snd subs) _e2 in
      let _ = match e2 with
	| Lvar p -> ()
	| Var v -> if ident_is_primed v then
	      (d_implication_error ("rhs |-> not implemented",subs,(EXC_FALSE_HPRED hpred2));
	       raise Exn.Abduction_Case_Not_implemented)
	| _ -> ()
      in
	(match prop_iter_create prop1 with
	  | None -> raise (IMPL_EXC ("lhs is empty",subs,EXC_FALSE))
	  | Some iter1 ->
	      (match prop_iter_find iter1 (filter_ne_lhs (fst subs) e2) with
		| None -> raise (IMPL_EXC ("lhs does not have e|->",subs,(EXC_FALSE_HPRED hpred2)))
		| Some iter1' ->
		    (match prop_iter_current iter1' with
		      | Hpointsto (e1,se1,t1),_ ->
			  (try
			      let subs',fld_frame,fld_missing = strexp_imply e1 calc_missing subs se1 se2 in
			      let () = (if calc_missing then
				let () = 
				  match fld_missing with
				    | Some fld_missing ->
					missing_fld := (Hpointsto(_e2,fld_missing,t1)) :: !missing_fld
				    | None -> () in
				let () =
				  match fld_frame with
				    | Some fld_frame ->
					frame_fld := (Hpointsto(e1,fld_frame,t1)) :: !frame_fld
				    | None -> ()
				in ()) in
			      let prop1' = prop_iter_remove_curr_then_to_prop iter1'
			      in (subs',prop1')
			    with
			      | IMPL_EXC _ when calc_missing ->
				  raise (MISSING_EXC "could not match |-> present on both sides"))
		      | Hlseg (Lseg_NE,para1,e1,f1,elist1),_ -> (** Unroll lseg *)
			  let n' = Var (create_fresh_primed_ident name_n) in
			  let (_, para_inst1) = hpara_instantiate para1 e1 n' elist1 in
			  let hpred_list1 = para_inst1@[mk_lseg Lseg_PE para1 n' f1 elist1] in
			  let iter1'' = prop_iter_update_current_by_list iter1' hpred_list1
			  in hpred_imply (nesting+1) calc_missing subs (prop_iter_to_prop iter1'') hpred2
		      | Hdllseg (Lseg_NE,para1,iF1,oB1,oF1,iB1,elist1), _ 
			  when exp_equal (exp_sub (fst subs) iF1) e2 -> (** Unroll dllseg forward *)
			  let n' = Var (create_fresh_primed_ident name_n) in
			  let (_, para_inst1) = hpara_dll_instantiate para1 iF1 oB1 n' elist1 in
			  let hpred_list1 = para_inst1@[mk_dllseg Lseg_PE para1 n' iF1 oF1 iB1 elist1] in
			  let iter1'' = prop_iter_update_current_by_list iter1' hpred_list1 
			  in hpred_imply (nesting+1) calc_missing subs (prop_iter_to_prop iter1'') hpred2
		      | Hdllseg (Lseg_NE,para1,iF1,oB1,oF1,iB1,elist1), _
			  when exp_equal (exp_sub (fst subs) iB1) e2 -> (** Unroll dllseg backward *)
			  let n' = Var (create_fresh_primed_ident name_n) in
			  let (_, para_inst1) = hpara_dll_instantiate para1 iB1 n' oF1 elist1 in
			  let hpred_list1 = para_inst1@[mk_dllseg Lseg_PE para1 iF1 oB1 iB1 n' elist1] in
			  let iter1'' = prop_iter_update_current_by_list iter1' hpred_list1 
			  in hpred_imply (nesting+1) calc_missing subs (prop_iter_to_prop iter1'') hpred2
		      | _ -> assert false
		    )
	      )
	)
  | Hlseg (k,para2,_e2,_f2,_elist2) -> (* for now ignore implications between PE and NE *)
      let e2,f2 = exp_sub (snd subs) _e2, exp_sub (snd subs) _f2 in
      let _ = match e2 with
	| Lvar p -> ()
	| Var v -> if ident_is_primed v then
	      (d_implication_error ("rhs |-> not implemented",subs,(EXC_FALSE_HPRED hpred2));
	       raise Exn.Abduction_Case_Not_implemented)
	| _ -> ()
      in
	if exp_equal e2 f2 && k==Lseg_PE then (subs,prop1)
	else
	  (match prop_iter_create prop1 with
	    | None -> raise (IMPL_EXC ("lhs is empty",subs,EXC_FALSE))
	    | Some iter1 ->
		(match prop_iter_find iter1 (filter_hpred (fst subs) (hpred_sub (snd subs) hpred2)) with
		  | None ->
		      let elist2 = List.map (fun e -> exp_sub (snd subs) e) _elist2 in
		      let _,para_inst2 = hpara_instantiate para2 e2 f2 elist2
		      in sigma_imply (nesting+1) false subs prop1 para_inst2 (* calc_missing is false as we're checking an instantiation of the original list *)
		  | Some iter1' ->
		      let elist2 = List.map (fun e -> exp_sub (snd subs) e) _elist2 in
		      let subs' = exp_list_imply calc_missing subs (f2::elist2) (f2::elist2) in (* force instantiation of existentials *)
		      let prop1' = prop_iter_remove_curr_then_to_prop iter1' in
		      let hpred1 = match prop_iter_current iter1' with
			| hpred1,None -> hpred1
			| hpred1,Some b ->
			    if b then missing_pi := Aneq(_e2,_f2) :: !missing_pi; (* for PE |- NE *)
			    hpred1
		      in match hpred1 with
			| Hlseg _ -> (subs',prop1')
			| Hpointsto _ -> (* unroll rhs list and try again *)
			    let n' = Var (create_fresh_primed_ident name_n) in
			    let (_, para_inst2) = hpara_instantiate para2 _e2 n' elist2 in
			    let hpred_list2 = para_inst2@[mk_lseg Lseg_PE para2 n' _f2 _elist2]
			    in sigma_imply (nesting+1) calc_missing subs prop1 hpred_list2
			| Hdllseg _ -> assert false
		)
	  )
  | Hdllseg (Lseg_PE,_,_,_,_,_,_) ->
      (d_implication_error ("rhs dllsegPE not implemented",subs,(EXC_FALSE_HPRED hpred2));
       raise Exn.Abduction_Case_Not_implemented)
  | Hdllseg (k,para2,iF2,oB2,oF2,iB2,elist2) -> (* for now ignore implications between PE and NE *)
      let iF2,oF2 = exp_sub (snd subs) iF2, exp_sub (snd subs) oF2 in
      let iB2,oB2 = exp_sub (snd subs) iB2, exp_sub (snd subs) oB2 in
      let _ = match oF2 with
	| Lvar p -> ()
	| Var v -> if ident_is_primed v then
	      (d_implication_error ("rhs dllseg not implemented",subs,(EXC_FALSE_HPRED hpred2));
	       raise Exn.Abduction_Case_Not_implemented)
	| _ -> ()
      in
      let _ = match oB2 with
	| Lvar p -> ()
	| Var v -> if ident_is_primed v then
	      (d_implication_error ("rhs dllseg not implemented",subs,(EXC_FALSE_HPRED hpred2));
	       raise Exn.Abduction_Case_Not_implemented)
	| _ -> ()
      in
	(match prop_iter_create prop1 with
	  | None -> raise (IMPL_EXC ("lhs is empty",subs,EXC_FALSE))
	  | Some iter1 ->
	      (match prop_iter_find iter1 (filter_hpred (fst subs) (hpred_sub (snd subs) hpred2)) with
		| None ->
		    let elist2 = List.map (fun e -> exp_sub (snd subs) e) elist2 in
		    let _,para_inst2 =
		      if exp_equal iF2 iB2 then
			hpara_dll_instantiate para2 iF2 oB2 oF2 elist2
		      else assert false  (** Only base case of rhs list considered for now *)
		    in sigma_imply (nesting+1) false subs prop1 para_inst2 (* calc_missing is false as we're checking an instantiation of the original list *)
		| Some iter1' -> (** Only consider implications between identical listsegs for now *)
		    let elist2 = List.map (fun e -> exp_sub (snd subs) e) elist2 in
		    let subs' = exp_list_imply calc_missing subs (iF2::oB2::oF2::iB2::elist2) (iF2::oB2::oF2::iB2::elist2) in (* force instantiation of existentials *)
		    let prop1' = prop_iter_remove_curr_then_to_prop iter1'
		    in (subs',prop1')
	      )
	) 

(** Check that [sigma1] implies [sigma2] and return two substitution
    instantiations for the primed variables of [sigma1] and [sigma2]
    and a frame. Raise IMPL_FALSE if the implication cannot be
    proven. *)
and sigma_imply nesting calc_missing subs prop1 sigma2 : (subst2 * prop) =
  E.d_indent nesting;
  E.d_strln "Current Implication";
  d_implication nesting subs (prop1,prop_of_sigma sigma2);
  try
    (match move_primed_lhs_from_front subs sigma2 with
      | [] ->
	  (subs,prop1)
      | hpred2::sigma2' ->
	  let normal_case () =
	    let (subs',prop1') =
	      try hpred_imply (nesting+1) calc_missing subs prop1 hpred2
	      with IMPL_EXC _ when calc_missing ->
		missing_sigma := hpred2::!missing_sigma;
		subs,prop1 in
	    let res = sigma_imply (nesting+1) calc_missing subs' prop1' sigma2'
	    in res
	  in
	    (match hpred2 with
	      | Hpointsto(_e2,se2,t) ->
		  (match exp_sub (snd subs) _e2 with
		    | Lfield(_e2',fld) ->
			let t' = match t with
			  | Sizeof _t ->
			      Sizeof (Tstruct [(fld,_t)])
			  | _ -> raise (Failure "sigma_imply: Unexpected non-sizeof type") in
			let hpred2' = Hpointsto (_e2',Estruct [(fld,se2)], t') 
			in sigma_imply (nesting+1) calc_missing subs prop1 (hpred2'::sigma2')
		    | _ -> normal_case ())
	      | _ -> normal_case ())
    )
  with IMPL_EXC _ when calc_missing ->
    missing_sigma := sigma2 @ !missing_sigma;
    subs,prop1
	      
(** Check that the atom is implied. Raise an IMPL_FALSE_XXX exception otherwise. *)
let _imply_atom (sub1,sub2) pi1 sigma1 a =
  let a' = atom_sub sub2 a in
  let pi1' = (pi_sub sub2 !missing_pi) @ pi1 in
  let sigma1' = (sigma_sub sub2 !missing_sigma) @ sigma1 in
  if not (atom_mem a' pi1')
  then match a' with
    | Aneq (e1,e2) ->
	if not (check_disequal (prop_of_sigma sigma1') e1 e2)
	then raise (IMPL_EXC ("rhs atom missing in lhs",(sub1,sub2),(EXC_FALSE_ATOM a)))
    | Aeq _ -> raise (IMPL_EXC ("rhs atom missing in lhs",(sub1,sub2),(EXC_FALSE_ATOM a)))

let imply_atom calc_missing (sub1,sub2) pi1 sigma1 a =
  try
    _imply_atom (sub1,sub2) pi1 sigma1 a
  with
    | IMPL_EXC _ when calc_missing ->
	missing_pi := a :: !missing_pi

(** Check pure implications before looking at the spatial part. Add
    necessary instantiations for equalities and check that instantiations
    are possible for disequalities. *)
let rec pre_check_pure_implication calc_missing subs pi1 pi2 =
  match pi2 with
  | [] -> subs
  | Aeq (e2_in,f2_in)::pi2' ->
      let e2,f2 = exp_sub (snd subs) e2_in, exp_sub (snd subs) f2_in in
      if exp_equal e2 f2 then pre_check_pure_implication calc_missing subs pi1 pi2'
      else
	(match e2,f2 with
	  | Var v2, f2 when ident_is_primed v2 ->
	      let sub2' = sub_join (snd subs) (sub_of_list [v2, f2])
	      in pre_check_pure_implication calc_missing (fst subs,sub2') pi1 pi2'
	  | e2, Var v2 when ident_is_primed v2 ->
	      let sub2' = sub_join (snd subs) (sub_of_list [v2, e2])
	      in pre_check_pure_implication calc_missing (fst subs,sub2') pi1 pi2'
	  | e2,f2 ->
	      let pi1' = pi_sub (fst subs) pi1 in
	      let _ = imply_atom calc_missing subs pi1' [] (Aeq (e2_in,f2_in))
	      in pre_check_pure_implication calc_missing subs pi1 pi2'
	)
  | Aneq (Var v,f2)::pi2' ->
      if not (ident_is_primed v || calc_missing)
      then raise (IMPL_EXC("ineq e2=f2 in rhs with e2 not primed var",(sub_empty,sub_empty),EXC_FALSE))
      else pre_check_pure_implication calc_missing subs pi1 pi2'
  | Aneq (e1,e2)::pi2' ->
      if calc_missing then pre_check_pure_implication calc_missing subs pi1 pi2'
      else raise (IMPL_EXC ("ineq e2=f2 in rhs with e2 not primed var",(sub_empty,sub_empty),EXC_FALSE))

(** [check_implication prop1 prop2] returns true if [prop1|-prop2] *)
let _check_implication calc_missing prop1 prop2 =
  let filter (id,e) =
    ident_is_normal id && fav_for_all (exp_fav e) ident_is_normal in
  let sub1_base = 
    sub_filter_pair filter (prop_get_sub prop1) in

  let pi1,pi2 = prop_get_pure prop1, prop_get_pure prop2 in
  let sigma1,sigma2 = prop_get_sigma prop1, prop_get_sigma prop2 in
  let subs = pre_check_pure_implication calc_missing (prop_get_sub prop1,sub1_base) pi1 pi2 in
  (* let subs = pre_check_pure_implication calc_missing (sub_empty,sub_empty) pi1 pi2 in *)
  let (sub1,sub2),frame = sigma_imply 0 calc_missing subs prop1 sigma2 in
  let pi1' = pi_sub sub1 pi1 in
  let sigma1' = sigma_sub sub1 sigma1 in
  let _ = List.iter (imply_atom calc_missing (sub1,sub2) pi1' sigma1') pi2
  in
    E.d_strln "+++++++++++ Implication";
    d_implication 0 (sub1,sub2) (prop1,prop2);
    E.d_strln"++++++++++++ returning TRUE@.";
    (sub1,sub2),(prop_get_sigma frame)


(** [check_implication_for_footprint p1 p2] returns
    [Some(sub,frame,missing)] if [sub(p1 * missing) |- sub(p2 *
    frame)] where [sub] is a substitution which instantiates the
    primed vars of [p1] and [p2], which are assumed to be disjoint. *)
let check_implication_for_footprint p1 p2 =
  try
    implication_lhs := p1;
    implication_rhs := p2;
    missing_pi := [];
    missing_sigma := [];
    frame_fld := [];
    missing_fld := [];
    let (sub1,sub2),frame = _check_implication true p1 p2
    in Some(sub1,sub2,frame,!missing_pi,!missing_sigma,!frame_fld,!missing_fld)
  with
    | IMPL_EXC (s,subs,body) ->
	d_implication_error (s,subs,body);
	None
    | MISSING_EXC s ->
	E.d_strln ("WARNING: footprint failed to find MISSING because: " ^ s);
	None

let __check_implication p1 p2 =
  try
    implication_lhs := p1;
    implication_rhs := p2;
    let subs,frame = _check_implication false p1 p2
    in
      if frame != [] then raise (IMPL_EXC("lhs leftover not empty",subs,EXC_FALSE))
      else true
  with
    | IMPL_EXC (s,subs,body) ->
	d_implication_error (s,subs,body);
	false
    | Exn.Abduction_Case_Not_implemented ->
	E.stderr "Warning: Abduction not implemented in __check_implication@.";
	false

let check_implication p1 p2 =
  let r = __check_implication p1 p2 && (if !Config.footprint then __check_implication (prop_extract_footprint p1) (prop_extract_footprint p2) else true)
  in r

(** Find miminum set of pi's whose disjunction is equivalent to true *)

let inconsistent_atom = function
  | Aeq (e1,e2) -> (match e1,e2 with
      | Const_int n, Const_int m -> n<>m
      | _ -> false)
  | Aneq (e1,e2) -> (match e1,e2 with
      | Const_int n, Const_int m -> n=m
      | _ -> (exp_compare e1 e2 = 0))

let inconsistent_pi pi =
  let fav_pi = pi_fav pi in
  let sub_list = List.map (fun id -> (id ,Var (create_fresh_normal_ident (ident_name id)))) (fav_to_list fav_pi) in
  let sub = sub_of_list sub_list in
  let pi' = pi_sub sub pi in
  let p = List.fold_left prop_atom_and prop_emp pi'
  in List.exists inconsistent_atom (prop_get_pure p)

let neg_atom = function
  | Aeq (e1,e2) -> Aneq (e1,e2)
  | Aneq (e1,e2) -> Aeq (e1,e2)

(** check if the pi's in [cases] cover true *)
let rec _is_cover acc_pi cases = match cases with
  | [] -> inconsistent_pi acc_pi
  | (pi,_)::cases' ->
      List.for_all (fun a -> _is_cover ((neg_atom a)::acc_pi) cases') pi

let is_cover cases = _is_cover [] cases

exception NO_COVER

(** Find miminum set of pi's in [cases] whose disjunction covers true *)
let find_minimum_pure_cover cases =
  let cases = 
    let compare (pi1,_) (pi2,_) = int_compare (List.length pi1) (List.length pi2)
    in List.sort compare cases in
  let rec grow seen todo = match todo with
    | [] -> raise NO_COVER
    | (pi,x)::todo' ->
	if is_cover ((pi,x)::seen) then (pi,x)::seen
	else grow ((pi,x)::seen) todo' in
  let rec _shrink seen todo = match todo with
    | [] -> seen
    | (pi,x)::todo' ->
	if is_cover (seen @ todo') then _shrink seen todo'
	else _shrink ((pi,x)::seen) todo' in
  let shrink cases =
    if List.length cases > 2 then _shrink [] cases
    else cases
  in try Some (shrink (grow [] cases))
    with NO_COVER -> None
