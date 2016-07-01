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

module F = Format
module S = Sil
module E = Error.MyErr (struct let mode = Error.DEFAULT end)

(*let () = E.set_mode Error.ALWAYS
let () = E.set_colour Error.green *)

let cil_exp_compare (e1:Cil.exp) (e2:Cil.exp) = Pervasives.compare e1 e2

(** Footprint frame. *)
type footprint =
    {foot_pi: atom list;
     foot_sigma: hpred list}

(** A proposition. The following invariants are mantained. [sub] is of
    the form id1=e1 ... idn=en where: the id's are distinct and do not
    occur in the e's nor in [pi] or [sigma]; the id's are in sorted
    order; the id's are not existentials; if idn=yn (for yn not
    existential) then idn<yn in the order on ident's. [pi] is sorted
    and normalized, and does not contain x=e. [sigma] is sorted and
    normalized. *)
type prop =
    {sub: subst;
     pi:atom list;
     sigma: hpred list;
     footprint: footprint option}

exception Bad_footprint
exception Cannot_star

(** Pure proposition. *)
type pure_prop = subst * atom list

(** {2 Basic Functions for Propositions} *)

(** {1 Functions for Comparison} *)

(** Comparison between lists of equalities and disequalities. Lexicographical order. *)
let rec pi_compare pi1 pi2 =
  if pi1==pi2 then 0
  else match (pi1,pi2) with
    | ([],[]) -> 0
    | ([],_::_) -> -1
    | (_::_,[]) -> 1
    | (a1::pi1',a2::pi2') ->
	let n = atom_compare a1 a2
	in if n<>0 then n
	  else pi_compare pi1' pi2'

let pi_equal pi1 pi2 =
  pi_compare pi1 pi2 = 0

(** Comparsion between lists of heap predicates. Lexicographical order. *)
let rec sigma_compare sigma1 sigma2 =
  if sigma1==sigma2 then 0
  else match (sigma1,sigma2) with
    | ([],[]) -> 0
    | ([],_::_) -> -1
    | (_::_,[]) -> 1
    | (h1::sigma1',h2::sigma2') ->
	let n = hpred_compare h1 h2
	in if n<>0 then n
	  else sigma_compare sigma1' sigma2'

let sigma_equal sigma1 sigma2 =
  sigma_compare sigma1 sigma2 = 0


let footprint_compare fp1 fp2 =
      let n = pi_compare fp1.foot_pi fp2.foot_pi
      in if n<>0 then n
	else sigma_compare fp1.foot_sigma fp2.foot_sigma

let footprint_equal fp1 fp2 = 
  footprint_compare fp1 fp2 = 0

let footprintop_compare fp1 fp2 = match fp1,fp2 with
  | None,None -> 0
  | None,Some _ -> -1
  | Some _,None -> 1
  | Some fp1,Some fp2 ->
      footprint_compare fp1 fp2

let footprintop_equal fp1 fp2 = 
  footprintop_compare fp1 fp2 = 0

(** Comparison between propositions. Lexicographical order. *)
let prop_compare p1 p2 =
  let n = sub_compare p1.sub p2.sub
  in if n<>0 then n
    else let n = pi_compare p1.pi p2.pi
      in if n<>0 then n
	else let n = sigma_compare p1.sigma p2.sigma
	  in if n<>0 then n
	    else footprintop_compare p1.footprint p2.footprint

let prop_equal p1 p2 = 
  (prop_compare p1 p2 = 0)

(** {1 Functions for Pretty Printing} *)

(** Print a sequence. *)
let rec pp_seq pp f = function
  | [] -> ()
  | [x] -> F.fprintf f "%a" pp x
  | x::l -> F.fprintf f "%a,%a" pp x (pp_seq pp) l

(** Print a *-separated sequence. *)
let rec pp_star_seq pp f = function
  | [] -> ()
  | [x] -> F.fprintf f "%a" pp x
  | x::l -> F.fprintf f "%a *@ %a" pp x (pp_star_seq pp) l

(** Pretty print a footprint. *)
let pp_footprint f = function
  | None -> ()
  | Some fp ->
      F.fprintf f "@,@[[footprint %a@ %s%a]@]"
	(pp_star_seq pp_atom) fp.foot_pi 
	(match fp.foot_pi with [] -> "" | _ -> " * ")
	(pp_star_seq pp_hpred) fp.foot_sigma

(** Pretty print a substitution. *)
let pp_sub f sub =
  let pi_sub = List.map (fun (id,e) -> Aeq(Var id,e)) (sub_to_list sub)
  in (pp_star_seq pp_atom) f pi_sub

(** Dump a substitution. *)
let d_sub (sub:subst) = Error.add_print_action (Error.PTsub, Obj.repr sub)

(** Pretty print a pi. *)
let pp_pi =
  pp_star_seq pp_atom

(** Dump a pi. *)
let d_pi (pi:Sil.atom list) = Error.add_print_action (Error.PTpi, Obj.repr pi)

(** Pretty print a sigma. *)
let pp_sigma =
  pp_star_seq pp_hpred

(** Dump a sigma. *)
let d_sigma (sigma:Sil.hpred list) = Error.add_print_action (Error.PTsigma, Obj.repr sigma)

(** Pretty print a proposition. *)
let pp_prop f prop =
  let pi_sub = List.map (fun (id,e) -> Aeq(Var id,e)) (sub_to_list prop.sub) in
  let pi = prop.pi @ pi_sub in
  let sigma = prop.sigma in
  let pp_pure f () =
    if pi != [] then F.fprintf f "@[%a@] *@ " pp_pi pi
  in F.fprintf f "@[<v>%a@[%a@]%a@]" pp_pure () pp_sigma sigma pp_footprint prop.footprint

(** Dump a proposition. *)
let d_prop (prop:prop) = Error.add_print_action (Error.PTprop, Obj.repr prop)

(** {1 Functions for computing free non-program variables} *)

let pi_fav_add fav pi =
  List.iter (atom_fav_add fav) pi

let pi_fav =
  fav_imperative_to_functional pi_fav_add

let sigma_fav_add fav sigma = 
  List.iter (hpred_fav_add fav) sigma

let sigma_fav =
  fav_imperative_to_functional sigma_fav_add

let footprint_fav_add fav footprint =
  match footprint with
    | None -> ()
    | Some fp ->
	pi_fav_add fav fp.foot_pi;
	sigma_fav_add fav fp.foot_sigma

let footprint_fav =
  fav_imperative_to_functional footprint_fav_add

let prop_fav_add fav prop =
  sub_fav_add fav prop.sub;
  pi_fav_add fav prop.pi;
  sigma_fav_add fav prop.sigma;
  footprint_fav_add fav prop.footprint

let prop_fav =
  fav_imperative_to_functional prop_fav_add

let prop_live_fav_add fav prop =
  sub_fav_add fav prop.sub;
  (if not !Config.footprint_analysis then pi_fav_add fav (List.filter (function Aeq _ -> true | _ -> false) prop.pi));
  sigma_fav_add fav prop.sigma;
  match prop.footprint with
  | None -> ()
  | Some footprint ->
      (if not !Config.footprint_analysis then pi_fav_add fav footprint.foot_pi);
      sigma_fav_add fav footprint.foot_sigma

let prop_live_fav =
  fav_imperative_to_functional prop_live_fav_add

let prop_fav =
  fav_imperative_to_functional prop_fav_add

let rec hpred_fav_in_pvars_add fav = function
  | Hpointsto (Lvar _, sexp, _) -> strexp_fav_add fav sexp 
  | Hpointsto _ | Hlseg _ | Hdllseg _ -> ()

let sigma_fav_in_pvars_add fav sigma =
  List.iter (hpred_fav_in_pvars_add fav) sigma

(** {1 Functions for computing free or bound non-program variables} *)

let pi_av_add fav pi =
  List.iter (atom_av_add fav) pi

let sigma_av_add fav sigma = 
  List.iter (hpred_av_add fav) sigma

let prop_av_add fav prop =
  sub_av_add fav prop.sub;
  pi_av_add fav prop.pi;
  sigma_av_add fav prop.sigma;
  match prop.footprint with
    | None -> ()
    | Some footprint ->
	pi_av_add fav footprint.foot_pi; sigma_av_add fav footprint.foot_sigma

let prop_av =
  fav_imperative_to_functional prop_av_add

(** {2 Functions for Subsitition} *)

let pi_sub (subst:subst) pi =
  let f = atom_sub subst
  in List.map f pi

let sigma_sub subst sigma = 
  let f = hpred_sub subst
  in List.map f sigma


(** {2 Functions for normalization} *)

(** This function assumes that if (x,Var(y)) in sub, then ident_compare x y = 1 *)
let sub_normalize sub =
  let f (id,e) = (not (ident_is_primed id)) && (not (ident_in_exp id e)) in
  let sub' = sub_filter_pair f sub in
  if sub_equal sub sub' then sub else sub'

let lift e = 
  match e with
  | Const_int n when (!Config.int_bound <= -n || !Config.int_bound <= n) -> 
      S.exp_get_undefined ()
  | _ -> e 

exception Contains_sizeof of exp

let rec exp_approx_eval e = 
  match e with
  | Var _ -> 
      e
  | Const_int _ ->
      lift e
  | Const_fun _ ->
      e
  | Cast (_, e1) ->
      assert false
  | UnOp (Cil.Neg, e1) ->
      begin
        match exp_approx_eval e1 with
        | Const_int n -> Const_int (-n)
        | _ -> S.exp_get_undefined () 
      end
  | UnOp (Cil.BNot, _) ->
      S.exp_get_undefined ()
  | UnOp (Cil.LNot, e1) ->
      S.exp_get_undefined ()
  | BinOp (Cil.PlusA, e1, e2) ->
      let e1' = exp_approx_eval e1 in
      let e2' = exp_approx_eval e2 in
      begin
        match e1', e2' with
        | Const_int 0, _ -> e2'
        | _, Const_int 0 -> e1'
        | Const_int n, Const_int m -> lift (Const_int (n+m))
        | _, _ -> S.exp_get_undefined ()
      end
  | BinOp (Cil.MinusA, e1, e2) ->
      let e1' = exp_approx_eval e1 in
      let e2' = exp_approx_eval e2 in
      begin
        match e1', e2' with
        | _, Const_int 0 -> e1'
        | Const_int n, Const_int m -> lift (Const_int (n-m))
        | _, _ -> S.exp_get_undefined ()
      end
  | BinOp (Cil.MinusPP, _, _) ->
      S.exp_get_undefined ()
  | BinOp (Cil.Mult, e1, e2) ->
      let e1' = exp_approx_eval e1 in
      let e2' = exp_approx_eval e2 in
      begin
        match e1', e2' with
        | Const_int 0, _ -> e1'
        | Const_int 1, _ -> e2'
        | _, Const_int 0 -> e2'
        | _, Const_int 1 -> e1'
        | Const_int n, Const_int m -> lift (Const_int (n*m))
        | _, _ -> S.exp_get_undefined ()
      end
  | BinOp (Cil.Div, e1, e2) ->
      let e1' = exp_approx_eval e1 in
      let e2' = exp_approx_eval e2 in
      begin
        match e1', e2' with
        | _, Const_int 0 -> S.exp_get_undefined ()
        | Const_int 0, _ | _, Const_int 1 -> e1'
        | Const_int n, Const_int m -> lift (Const_int (n/m))
        | _, _ -> S.exp_get_undefined ()
      end
  | BinOp (Cil.Mod, e1, e2) ->
      let e1' = exp_approx_eval e1 in
      let e2' = exp_approx_eval e2 in
      begin
        match e1', e2' with
        | _, Const_int 0 -> S.exp_get_undefined ()
        | Const_int 0, _ -> e1'
        | _, Const_int 1 -> Const_int 0
        | Const_int n, Const_int m -> lift (Const_int (n mod m))
        | _, _ -> S.exp_get_undefined ()
      end
  | BinOp (Cil.Shiftlt, _, _) | BinOp (Cil.Shiftrt, _, _) ->
      S.exp_get_undefined ()
  | BinOp (Cil.Lt, _, _) | BinOp (Cil.Gt, _, _) 
  | BinOp (Cil.Le, _, _) | BinOp (Cil.Ge, _, _) 
  | BinOp (Cil.Eq, _, _) | BinOp (Cil.Ne, _, _) ->
      assert false
  | BinOp (Cil.BAnd, _, _) | BinOp (Cil.BXor, _, _) | BinOp (Cil.BOr, _, _) ->
      S.exp_get_undefined ()
  | BinOp (Cil.LAnd, e1, e2) | BinOp (Cil.LOr, e1, e2) ->
      assert false
  | BinOp _ -> assert false
  | Lvar _  ->
      e
  | Lfield (Var _,_) | Lfield (Lvar _, _) ->
      e
  | Lfield (e1,fld) ->
      let e1' = exp_approx_eval e1 in 
      Lfield (e1', fld)
  | Lindex (Var _,Var _) ->
      e
  | Lindex (e1,e2) ->
      let e1' = match exp_approx_eval e1 with
        | Var _ as e1' -> e1' 
        | _ -> S.exp_get_undefined () in
      let e2' = match exp_approx_eval e2 with
        | Var _ as e2' -> e2' 
        | _ -> S.exp_get_undefined () in
      Lindex(e1', e2')
  | Sizeof _ ->
      raise (Contains_sizeof e)

let rec exp_approx e = 
  match e with
  | Var _ | Const_int _ | Const_fun _ | Cast _ | Sizeof _ -> 
      exp_approx_eval e
  | UnOp (Cil.LNot, e1) -> 
      begin
        match exp_approx e1 with
        | Const_int 0 -> Const_int 1
        | Const_int _ -> Const_int 0
        | UnOp(Cil.LNot,e1') -> e1'
        | e1' -> UnOp(Cil.LNot, e1') 
      end
  | UnOp _ ->
      exp_approx_eval e
  | BinOp (Cil.Le, e1, e2) -> 
      begin
        match exp_approx e1, exp_approx e2 with
        | Const_int n, Const_int m -> if n <= m then Const_int 1 else Const_int 0
        | e1',e2' -> BinOp (Cil.Le, e1', e2') 
      end 
  | BinOp (Cil.Lt, e1, e2) -> 
      begin
        match exp_approx e1, exp_approx e2 with
        | Const_int n, Const_int m -> if n < m then Const_int 1 else Const_int 0
        | e1',e2' -> BinOp (Cil.Lt, e1', e2') 
      end 
  | BinOp (Cil.Ge, e1, e2) -> 
      begin
        match exp_approx e1, exp_approx e2 with
        | Const_int n, Const_int m -> if n >= m then Const_int 1 else Const_int 0
        | e1',e2' -> BinOp (Cil.Ge, e1', e2') 
      end 
  | BinOp (Cil.Gt, e1, e2) ->
      begin
        match exp_approx e1, exp_approx e2 with
        | Const_int n, Const_int m -> if n > m then Const_int 1 else Const_int 0
        | e1',e2' -> BinOp (Cil.Gt, e1', e2') 
      end 
  | BinOp (Cil.Eq, e1, e2) ->
      begin
        match exp_approx e1, exp_approx e2 with
        | Const_int n, Const_int m -> if n = m then Const_int 1 else Const_int 0
        | e1',e2' -> BinOp (Cil.Eq, e1', e2') 
      end 
  | BinOp (Cil.Ne, e1, e2) ->
      begin
        match exp_approx e1, exp_approx e2 with
        | Const_int n, Const_int m -> if n <> m then Const_int 1 else Const_int 0
        | e1',e2' -> BinOp (Cil.Ne, e1', e2') 
      end 
  | BinOp (Cil.LAnd, e1, e2) ->
      let e1' = exp_approx e1 in
      let e2' = exp_approx e2 in
      begin
        match e1', e2' with
        | Const_int 0, _ -> e1'
        | Const_int n, _ -> e2'
        | _, Const_int 0 -> e2'
        | _, Const_int n -> e1'
        | _ -> BinOp (Cil.LAnd, e1', e2')
      end
  | BinOp (Cil.LOr, e1, e2) ->
      let e1' = exp_approx e1 in
      let e2' = exp_approx e2 in
      begin
        match e1', e2' with
        | Const_int 0, _ -> e2'
        | Const_int n, _ -> e1'
        | _, Const_int 0 -> e1'
        | _, Const_int n -> e2'
        | _ -> BinOp (Cil.LOr, e1', e2')
      end
  | BinOp _ ->
      exp_approx_eval e
  | Lvar _ | Lfield _ | Lindex _ ->
      exp_approx_eval e

let rec sym_eval e = match e with
  | Var _ -> 
      e
  | Const_int _ | Sizeof _ | Const_fun _ ->
      e
  | Cast (_, e1) ->
      sym_eval e1
  | UnOp (op, e1) ->
      let e1' = sym_eval e1 in 
      begin
        match op, e1' with
        | Cil.Neg, (UnOp(Cil.Neg,e2')) -> e2'
        | Cil.Neg, Const_int n -> Const_int (-n)
        | Cil.BNot, (UnOp(Cil.BNot,e2')) -> e2'
        | Cil.LNot, Const_int 0 -> Const_int 1
        | Cil.LNot, Const_int _ -> Const_int 0
        | Cil.LNot, (UnOp(Cil.LNot,e2')) -> e2'
        | _ -> UnOp(op, e1')
      end
  | BinOp (op, e1, e2) ->
      let e1' = sym_eval e1 in
      let e2' = sym_eval e2 in 
      begin
        match op, e1', e2' with
        | Cil.PlusA, Const_int 0, _ -> e2'
        | Cil.PlusA, _, Const_int 0 -> e1'
        | Cil.PlusA, Const_int n, Const_int m -> Const_int (n+m)
        | Cil.MinusA, Const_int 0, _ -> sym_eval (UnOp(Cil.Neg, e2'))
        | Cil.MinusA, _, Const_int 0 -> e1'
        | Cil.MinusA, Const_int n, Const_int m -> Const_int (n-m)
        | Cil.Mult, Const_int 1, _ -> e2'
        | Cil.Mult, _, Const_int 1 -> e1'
        | Cil.Mult, Const_int -1, _ -> sym_eval (UnOp(Cil.Neg, e2'))
        | Cil.Mult, _, Const_int -1 -> sym_eval (UnOp(Cil.Neg, e1'))
        | Cil.Mult, Const_int 0, _ -> Const_int 0
        | Cil.Mult, _, Const_int 0 -> Const_int 0
        | Cil.Mult, Const_int n, Const_int m -> Const_int (n*m)
        | Cil.Le, Const_int n, Const_int m -> 
            if n <= m then Const_int 1 else Const_int 0
        | Cil.Lt, Const_int n, Const_int m -> 
            if n < m then Const_int 1 else Const_int 0
        | Cil.Ge, Const_int n, Const_int m -> 
            if n >= m then Const_int 1 else Const_int 0
        | Cil.Gt, Const_int n, Const_int m -> 
            if n > m then Const_int 1 else Const_int 0
        | Cil.Eq, Const_int n, Const_int m -> 
            if n = m then Const_int 1 else Const_int 0
        | Cil.Ne, Const_int n, Const_int m -> 
            if n <> m then Const_int 1 else Const_int 0
        | Cil.BOr, Const_int 0, _ -> e2'
        | Cil.BOr, _, Const_int 0 -> e1'
        | Cil.BAnd, Const_int 0, _ -> e1'
        | Cil.BAnd, _, Const_int 0 -> e2'
        | Cil.LAnd, Const_int 0, _ -> e1'
        | Cil.LAnd, Const_int n, _ -> e2'
        | Cil.LAnd, _, Const_int 0 -> e2'
        | Cil.LAnd, _, Const_int n -> e1'
        | Cil.LOr, Const_int 0, _ -> e2'
        | Cil.LOr, Const_int n, _ -> e1'
        | Cil.LOr, _, Const_int 0 -> e1'
        | Cil.LOr, _, Const_int n -> e2'
        | _ -> BinOp(op, e1',e2')
      end
  | Lvar _  ->
      e
  | Lfield (e1,fld) ->
      let e1' = sym_eval e1 in 
      Lfield (e1', fld)
  | Lindex (e1,e2) ->
      let e1' = sym_eval e1 in
      let e2' = sym_eval e2 in 
      Lindex (e1',e2')

let rec exp_normalize sub exp =
  let exp' = exp_sub sub exp in
    try
      if !Config.abs_val >= 1 then exp_approx exp' 
      else sym_eval exp'
    with
	Contains_sizeof e -> e

(* let exp_normalize sub exp = exp_sub sub exp *)

let atom_normalize sub a = 
  let rec f eq e1 e2 = 
    match e1, e2 with
    | Lfield (e1',fld1), Lfield (e2',fld2) ->
        if not (fld_equal fld1 fld2) then eq
        else (f (e1',e2') e1' e2') 
    | Lindex (e1',idx1), Lindex (e2', idx2) -> 
        (* Hongseok's comment: possibly unsound *)
        (* if not (exp_equal idx1 idx2) then eq else *)
        (f (e1',e2') e1' e2') 
    | _ -> eq in
  match atom_sub sub a with
  | Aeq (e1,e2) ->
      let (e1',e2') = f (e1,e2) e1 e2 in
      if exp_compare e1' e2' <= 0 then Aeq (e1',e2')
      else Aeq(e2',e1')
  | Aneq (e1,e2) ->
      if exp_compare e1 e2 <= 0 then Aneq (e1,e2) 
      else Aneq(e2,e1)

let rec remove_duplicates_from_sorted special_equal = function
  | [] -> []
  | [x] -> [x]
  | x::y::l -> 
      if (special_equal x y) 
      then remove_duplicates_from_sorted special_equal (y::l)
      else x::(remove_duplicates_from_sorted special_equal (y::l))

let rec strexp_normalize sub se = 
  match se with
  | Eexp e -> 
      Eexp (exp_normalize sub e)
  | Estruct fld_cnts ->
    begin
      match fld_cnts with 
      | [] -> se
      | _ ->
         let fld_cnts' = 
           List.map (fun (fld,cnt) -> 
             fld,strexp_normalize sub cnt) fld_cnts in
         let fld_cnts'' = List.sort fld_strexp_compare fld_cnts' in 
         Estruct fld_cnts'' 
    end
  | Earray (size, idx_cnts) ->
    begin
      match idx_cnts with
      | [] -> se
      | _ ->
        if !Config.array_level >= 1 then Earray (size, [])
        else
          let idx_cnts' = 
            List.map (fun (idx,cnt) -> 
              exp_normalize sub idx, strexp_normalize sub cnt) idx_cnts in
          let idx_cnts'' = 
            List.sort exp_strexp_compare idx_cnts' in 
          Earray (size, idx_cnts'')
    end

let rec hpred_normalize sub = function
  | Hpointsto (root, cnt, te) -> 
      let normalized_root = exp_normalize sub root in
      let normalized_cnt = strexp_normalize sub cnt in
      let normalized_te = exp_normalize sub te
      in Hpointsto (normalized_root, normalized_cnt, normalized_te)
  | Hlseg (k, para, e1, e2, elist) ->
      let normalized_e1 = exp_normalize sub e1 in
      let normalized_e2 = exp_normalize sub e2 in
      let normalized_elist = List.map (exp_normalize sub) elist in
      let normalized_para = hpara_normalize sub para 
      in Hlseg (k, normalized_para, normalized_e1, normalized_e2, normalized_elist)
  | Hdllseg (k, para, e1, e2,e3,e4, elist) ->
      let norm_e1 = exp_normalize sub e1 in
      let norm_e2 = exp_normalize sub e2 in
      let norm_e3 = exp_normalize sub e3 in
      let norm_e4 = exp_normalize sub e4 in
      let norm_elist = List.map (exp_normalize sub) elist in
      let norm_para = hpara_dll_normalize sub para 
      in Hdllseg (k, norm_para, norm_e1, norm_e2, norm_e3, norm_e4, norm_elist)

and hpara_normalize sub para =
  let normalized_body = List.map (hpred_normalize sub_empty) (para.body) in
  let sorted_body = List.sort hpred_compare normalized_body 
  in {para with body = sorted_body}

and hpara_dll_normalize sub para =
  let normalized_body = List.map (hpred_normalize sub_empty) (para.body_dll) in
  let sorted_body = List.sort hpred_compare normalized_body 
  in {para with body_dll = sorted_body}




let pi_normalize sub pi =
  let filter_useful_atom = function
    | Aeq(Const_int n, Const_int m) -> n<>m
    | Aneq(Const_int n, Const_int m) -> n=m
    | _ -> true in
  let pi' = List.filter filter_useful_atom (pi_sub sub pi)
  in if pi_equal pi pi' then pi
    else remove_duplicates_from_sorted atom_equal (List.stable_sort atom_compare pi')

let sigma_normalize sub sigma =
  let sigma' =
    List.stable_sort hpred_compare (List.map (hpred_normalize sub) sigma)
  in if sigma_equal sigma sigma' then sigma else sigma'

let footprint_normalize footprint =
  let npi = pi_normalize sub_empty footprint.foot_pi in
  let nsigma = sigma_normalize sub_empty footprint.foot_sigma 
  in {foot_pi = npi; foot_sigma = nsigma}

let exp_normalize_prop prop exp = 
  exp_normalize prop.sub exp

let atom_normalize_prop prop atom =
  atom_normalize prop.sub atom

let strexp_normalize_prop prop strexp =
  strexp_normalize prop.sub strexp

let hpred_normalize_prop prop hpred =
  hpred_normalize prop.sub hpred

let sigma_normalize_prop prop sigma =
  sigma_normalize prop.sub sigma

(** {2 Function for replacing occurrences of expressions.} *)

let rec sigma_replace_exp epairs sigma =
  let sigma' = List.map (hpred_replace_exp epairs) sigma
  in sigma_normalize sub_empty sigma'

(** {2 Query about Proposition} *)

(** Check if the sigma part of the proposition is emp *)
let prop_is_emp p = match p.sigma with
  | [] -> true
  | _ -> false

(** {2 Functions for changing and generating propositions} *)

(** Construct a disequality. *)
let mk_neq e1 e2 =
  atom_normalize sub_empty (Aneq (e1,e2))

(** Construct a pointsto. *)
let mk_ptsto lexp sexp te =
  let nsexp = strexp_normalize sub_empty sexp 
  in Hpointsto(lexp,nsexp,te)

let unstructured_type = function
  | Tstruct _ | Tarray _ -> false
  | _ -> true

(** Construct a points-to predicate for an expression using either the provided expression [name] as
    base for fresh identifiers. *)
let mk_ptsto_exp name (exp,te,expo) : hpred =  
  let default_strexp () = match te with
    | Sizeof typ ->
	(match typ with
	  | Tint | Tfloat | Tvoid  | Tfun | Tptr _ ->
	      let rv' = (if !Config.footprint then create_fresh_footprint_ident else create_fresh_primed_ident) name_siltmp (* name *) in
		Eexp (Var rv')
	  | Tstruct ftl -> Estruct []
	  | Tarray (_,n) -> Earray (n,[])
	  | Tvar name -> 
	      E.err "@[<2>ANALYSIS BUG@\n";
	      E.err "type %a should be expanded to " pp_typ_full typ; 
	      (match Sil.tenv_lookup name with 
		| None -> E.err "nothing@\n@."
		| Some typ' -> E.err "%a@\n@." pp_typ_full typ');
	      assert false)
    | Var id ->
	  Estruct []
    | te ->
	E.stderr "trying to create ptsto with type: %a@\n@." pp_texp_full te;
	assert false in
  let strexp = match expo with
    | Some e -> Eexp e
    | None -> default_strexp () in 
    mk_ptsto exp strexp te


let sort_ftl ftl =
  let compare (f1,_) (f2,_) = fld_compare f1 f2
  in List.sort compare ftl

let pp_off fmt off =
  List.iter (fun n -> F.fprintf fmt "%a " pp_name n) off

let rec create_struct_values kind max_stamp t off : strexp =
 match t,off with
  | Tstruct ftl,[] ->
      Estruct []
  | Tstruct ftl,f::off' ->
      let _,t' = try List.find (fun (f',_) -> name_equal f f') ftl
	with Not_found -> raise Bad_footprint in
      let se = create_struct_values kind max_stamp t' off'
      in Estruct [(f,se)]
  | Tarray (t,n),[] ->
      Earray(n,[])
  | Tarray (t,n),_ -> assert false
  | Tint,_ | Tfloat,_ | Tvoid,_  | Tfun,_ | Tptr _ ,_->
      if off != [] then
	(E.stderr "create_struct_values type:%a off:%a@." pp_typ_full t pp_off off;
	 raise Bad_footprint);
      incr max_stamp;
      let id = create_ident kind name_siltmp !max_stamp
      in Eexp (Var id)
  | Tvar _,_ ->
      E.stderr "create_struct_values type:%a off:%a@." pp_typ_full t pp_off off;
      assert false

let rec collect_root_offset exp = match exp with
  | Var _ | Const_int _ | Const_fun _ | Sizeof _ | UnOp _ | BinOp _ | Lvar _ ->
      exp,[]
  | Lfield (e,f) ->
      let roote,off = collect_root_offset e
      in roote,off@[f]
  | Lindex _ -> assert false
  | Cast _ -> assert false

let collect_offset exp =
  snd (collect_root_offset exp)

let strexp_extend_values kind max_stamp se typ off = match off with
  | [] -> se
  | f::off' ->
      let fsel,ftl = match se,typ with
	|  Estruct fsel, Tstruct ftl -> fsel,ftl
	| _ -> raise Bad_footprint in
      let se' =
	try snd (List.find (fun (f',se') -> name_equal f f') fsel)
	with Not_found ->
	  let typ' = try snd (List.find (fun (f',t') -> name_equal f f') ftl)
	    with Not_found -> raise Bad_footprint
	  in create_struct_values kind max_stamp typ' off' in
      let fsel' = List.filter (fun (f',_) -> not (name_equal f f')) fsel
      in Estruct (List.sort fld_strexp_compare ((f,se')::fsel'))

(** Find the type of [exp] if it occurs in [strexp] *)
let rec find_exp_type_se exp strexp typ = match strexp,typ with
  | Eexp e,typ -> if exp_equal e exp then Some typ else None
  | Estruct fsel, Tstruct ftl -> find_exp_type_str exp (fsel,ftl)
  | _ -> None

and find_exp_type_str exp = function
  | (f,se)::fsel, (f',t)::ftl ->
      (match fld_compare f f' with
	| 0 ->
	    let res = find_exp_type_se exp se t
	    in if res==None then find_exp_type_str exp (fsel,ftl)
	      else res
	| n when n<0 -> find_exp_type_str exp (fsel,(f',t)::ftl)
	| _ -> find_exp_type_str exp ((f,se)::fsel,ftl))
  | [],_ -> None
  | _,[] -> None

(** Find the type of [exp] if it occurs in the hpred *)
let rec find_exp_type_hpred exp = function
  | Hpointsto(_,se,Sizeof t) ->
      find_exp_type_se exp se t
  | Hpointsto _ -> assert false
  | Hlseg (_,hpara,e1,e2,el) ->
      if List.exists (fun e' -> exp_equal e' exp) (e2::el) then
	(let _,sigma = hpara_instantiate hpara e1 e2 el
	  in find_exp_type_sigma exp sigma)
      else None
  | Hdllseg (_,hpara_dll,iF,oB,oF,iB,elist) ->
      if List.exists (fun e' -> exp_equal e' exp) (oB::oF::elist) then
	(let _,sigma = hpara_dll_instantiate hpara_dll iF oB oF elist
	  in find_exp_type_sigma exp sigma)
      else None

and find_exp_type_sigma exp = function
  | [] -> None
  | hpred::sigma' ->
      let res = find_exp_type_hpred exp hpred
      in if res==None then find_exp_type_sigma exp sigma'
	else res

(** Find the type of [exp] if it occurs in [sigma] *)
let find_pointed_type sigma exp =
  let expand_type = function
    | Tvar tn ->
	(match tenv_lookup tn with
	  | Some typ -> typ
	  | None -> assert false)
    | t -> t
  in match find_exp_type_sigma exp sigma with
    | None ->
	(* E.stderr "NOT FOUND@."; *)
	None
    | Some (Tptr typ') ->
	let typ'' = expand_type typ' in
	  (* E.stderr "FOUND TYPE %a@." pp_typ_full typ''; *)
	  Some typ''
    | Some _ ->
	(* E.stderr "NOT FOUND OF PTR TYPE@."; *)
	None

(** Find the root type of [exp_root]: if it is a pointer to a field of
    a struct, return the type of the struct, by looking for a dangling
    pointer to [exp_root] in the footprint part *)
let find_root_type footprint exp_root off typ =
  if off!=[] then match typ with
    | Tstruct _ -> typ
    | _ ->
	(*
	  E.stderr "In sigma:@.%a@." pp_sigma footprint.foot_sigma;
	  E.stderr "Looking for: %a@." pp_exp exp_root;
	*)
	let sigma = footprint.foot_sigma
	in (match find_pointed_type sigma exp_root with
	  | Some typ' -> typ'
	  | None -> typ)
  else typ

(** Construct a points-to predicate for an expression, to add to a
    footprint. *)
let mk_ptsto_exp_footprint footprint (exp_root,exp,typ) max_stamp : hpred =
  let e_root,off = collect_root_offset exp in
  let typ = find_root_type footprint exp_root off typ in
  let strexp =
    if off==[] && typ==Tfun then
      (match exp with
	| Lvar pvar ->
	    let fun_name = pvar_get_name pvar
	    in Eexp (Const_fun fun_name)
	| _ -> create_struct_values kfootprint max_stamp typ off
      )
    else create_struct_values kfootprint max_stamp typ off
  in mk_ptsto exp_root strexp (Sizeof typ)

(** Construct a points-to predicate for a single program variable. *)
let mk_ptsto_lvar ((pvar:pvar),typ,expo) : hpred =
  mk_ptsto_exp (pvar_get_name pvar) (Lvar pvar,Sizeof typ,expo)

(** Construct a lseg predicate *)
let mk_lseg k para e_start e_end es_shared =
  let npara = hpara_normalize sub_empty para 
  in Hlseg (k, npara, e_start, e_end, es_shared)

(** Construct a dllseg predicate *)
let mk_dllseg k para exp_iF exp_oB exp_oF exp_iB exps_shared = 
  let npara = hpara_dll_normalize sub_empty para 
  in Hdllseg (k, npara, exp_iF, exp_oB ,exp_oF, exp_iB, exps_shared)

(** Construct a hpara *)
let mk_hpara root next svars evars body =
  let para = {root=root; next=next; svars=svars; evars=evars; body=body}
  in hpara_normalize sub_empty para

(** Construct a dll_hpara *)
let mk_dll_hpara iF oB oF svars evars body =
  let para = {cell=iF; blink=oB; flink=oF; svars_dll=svars; evars_dll=evars; body_dll=body}
  in hpara_dll_normalize sub_empty para

(** Proposition [true /\ emp]. *)
let prop_emp : prop  = {sub=sub_empty; pi=[];sigma=[]; footprint=None}

(** Conjoin a heap predicate by separating conjunction. *)
let prop_hpred_star (p : prop) (h : hpred) : prop = 
  let sigma' = sigma_normalize p.sub (h::p.sigma)
  in {p with sigma=sigma'}

let prop_sigma_star (p : prop) (sigma : hpred list) : prop =
  let sigma' = sigma_normalize p.sub (sigma@p.sigma)
  in {p with sigma=sigma'}

let hpred_lhs_compare hpred1 hpred2 = match hpred1,hpred2 with
  | Hpointsto(e1,_,_),Hpointsto(e2,_,_) -> exp_compare e1 e2
  | Hpointsto _,_ -> -1
  | _,Hpointsto _ -> 1
  | hpred1,hpred2 -> hpred_compare hpred1 hpred2

let rec fsel_star_fld fsel1 fsel2 = match fsel1,fsel2 with
  | [],fsel2 -> fsel2
  | fsel1,[] -> fsel1
  | (f1,se1)::fsel1',(f2,se2)::fsel2' ->
      (match name_compare f1 f2 with
	| 0 -> (f1,sexp_star_fld se1 se2) :: fsel_star_fld fsel1' fsel2'
	| n when n<0 -> (f1,se1) :: fsel_star_fld fsel1' fsel2
	| _ -> (f2,se2) :: fsel_star_fld fsel1 fsel2')

and sexp_star_fld se1 se2 : strexp = match se1,se2 with
  | Estruct fsel1, Estruct fsel2 ->
      Estruct (fsel_star_fld fsel1 fsel2)
  | _ ->
      E.d_str "cannot star ";
      Sil.d_sexp se1; E.d_str " and "; Sil.d_sexp se2;
      E.d_ln ();
      assert false

let hpred_star_fld (hpred1 : hpred) (hpred2 : hpred) : hpred = match hpred1,hpred2 with
  | Hpointsto(e1,se1,t1),Hpointsto(_,se2,_) ->
      Hpointsto(e1,sexp_star_fld se1 se2,t1)
  | _ -> assert false

(** Implementation of [*] for the field-splitting model *)
let sigma_star_fld (sigma1 : hpred list) (sigma2 : hpred list) : hpred list =
  let sigma1 = List.stable_sort hpred_lhs_compare sigma1 in
  let sigma2 = List.stable_sort hpred_lhs_compare sigma2 in
  (* E.err "@.@. computing %a@.STAR @.%a@.@." pp_sigma sigma1 pp_sigma sigma2; *)
  let rec star sg1 sg2 : hpred list = match sg1,sg2 with
    | [],sigma2 -> []
    | sigma1,[] -> sigma1
    | hpred1::sigma1',hpred2::sigma2' ->
	(match hpred_lhs_compare hpred1 hpred2 with
	  | 0 -> hpred_star_fld hpred1 hpred2 :: star sigma1' sigma2'
	  | n when n<0 -> hpred1 :: star sigma1' sg2
	  | _ -> star sg1 sigma2')
  in try star sigma1 sigma2
    with _ ->
      E.d_str "cannot star ";
      d_sigma sigma1; E.d_str " and "; d_sigma sigma2;
      E.d_ln ();
      raise Cannot_star

(** Eliminates all empty lsegs from sigma, and collect equalities 
    The empty lsegs include 
    (a) "lseg_pe para 0 e elist",
    (b) "dllseg_pe para iF oB oF iB elist" with iF=0 or iB=0,
    (c) "lseg_pe para e1 e2 elist" and the rest of sigma contains the "cell" e1,
    (d) "dllseg_pe para iF oB oF iB elist" and the rest of sigma contains
    cell iF or iB. *)

module ExpSet =
  Set.Make(struct
    type t = exp 
    let compare = exp_compare
  end)

let sigma_remove_emptylseg sigma = 
  let alloc_set = 
    let rec f_alloc set = function 
      | [] -> 
          set
      | Hpointsto (e,_,_) :: sigma' | Hlseg (Lseg_NE,_,e,_,_) :: sigma' ->
          f_alloc (ExpSet.add e set) sigma'
      | Hdllseg (Lseg_NE,_,iF,_,_,iB,_) :: sigma' ->
          f_alloc (ExpSet.add iF (ExpSet.add iB set)) sigma'
      | _ :: sigma' ->
          f_alloc set sigma' in
    f_alloc ExpSet.empty sigma 
  in
  let rec f eqs_zero sigma_passed = function
    | [] -> 
        (List.rev eqs_zero, List.rev sigma_passed)
    | Hpointsto _ as hpred :: sigma' ->
        f eqs_zero (hpred :: sigma_passed) sigma'
    | Hlseg (Lseg_PE, _, e1, e2, _) :: sigma' 
        when (exp_equal e1 (Const_int 0)) || (ExpSet.mem e1 alloc_set) ->
        f (Aeq(e1,e2) :: eqs_zero) sigma_passed sigma'
    | Hlseg _ as hpred :: sigma' ->
	f eqs_zero (hpred :: sigma_passed) sigma'
    | Hdllseg (Lseg_PE, _, iF, oB, oF, iB, _) :: sigma' 
	when (exp_equal iF (Const_int 0)) || (ExpSet.mem iF alloc_set) 
          || (exp_equal iB (Const_int 0)) || (ExpSet.mem iB alloc_set) ->
        f (Aeq(iF,oF)::Aeq(iB,oB)::eqs_zero) sigma_passed sigma'
    | Hdllseg _ as hpred :: sigma' ->
	f eqs_zero (hpred :: sigma_passed) sigma' 
  in 
  f [] [] sigma

let sigma_intro_nonemptylseg e1 e2 sigma = 
  let rec f sigma_passed = function
    | [] -> 
        List.rev sigma_passed
    | Hpointsto _ as hpred :: sigma' ->
        f (hpred :: sigma_passed) sigma'
    | Hlseg (Lseg_PE, para, f1, f2, shared) :: sigma' 
        when (exp_equal e1 f1 && exp_equal e2 f2)
          || (exp_equal e2 f1 && exp_equal e1 f2) ->
        f (Hlseg (Lseg_NE, para, f1, f2, shared) :: sigma_passed) sigma'
    | Hlseg _ as hpred :: sigma' ->
	f (hpred :: sigma_passed) sigma'
    | Hdllseg (Lseg_PE, para, iF, oB, oF, iB, shared) :: sigma' 
        when (exp_equal e1 iF && exp_equal e2 oF)
          || (exp_equal e2 iF && exp_equal e1 oF) 
          || (exp_equal e1 iB && exp_equal e2 oB)
          || (exp_equal e2 iB && exp_equal e1 oB) ->
        f (Hdllseg (Lseg_NE, para, iF, oB, oF, iB, shared) :: sigma_passed) sigma' 
    | Hdllseg _ as hpred :: sigma' ->
	f (hpred :: sigma_passed) sigma' 
  in
  f [] sigma 


(** Conjoin a pure atomic predicate by normal conjunction. *)
let rec prop_atom_and ?(footprint=false) (p : prop) (a : atom) : prop =
  let a' = atom_normalize p.sub a in
  if List.mem a' p.pi then p else
  let p' =
    match a' with
    | Aeq (Var i, e) when ident_in_exp i e -> p
    | Aeq (Var i, e) ->
  	let sub_list = [(i, e)] in
	let mysub = sub_of_list sub_list in
	let sub' = sub_join mysub (sub_range_map (exp_sub mysub) p.sub) in
	let (nsub',npi',nsigma') = 
          (sub_normalize sub', pi_normalize sub' p.pi, sigma_normalize sub' p.sigma) in
	let (eqs_zero,nsigma'') = sigma_remove_emptylseg nsigma' in
	let p' = {p with sub=nsub'; pi=npi'; sigma=nsigma''}
	in List.fold_left (prop_atom_and ~footprint:footprint) p' eqs_zero
    | Aeq (e1,e2) when (exp_compare e1 e2 = 0)  -> p
    | Aneq (e1, e2) ->
	let pi' = pi_normalize p.sub (a'::p.pi) in
	let sigma' = sigma_intro_nonemptylseg e1 e2 p.sigma 
	in {p with pi=pi'; sigma=sigma'}
    | _ ->
	let pi' = pi_normalize p.sub (a'::p.pi)
	in {p with pi=pi'}
  in
    if footprint 
    then
      let footprint = match p'.footprint with
	| None -> assert false
	| Some footprint -> footprint in
      let fav_a' = atom_fav a' in
      let fav_nofootprint_a' =
	fav_copy_filter_ident fav_a' (fun id -> not (ident_is_footprint id)) in
      let fav_nofootprint_noprimed_a' = 
	fav_copy_filter_ident fav_nofootprint_a' (fun id -> not (ident_is_primed id)) in
      let predicate_warning = 
        not (fav_is_empty fav_nofootprint_a') in
      let predicate_fault =
        not (fav_is_empty fav_nofootprint_noprimed_a') in
      let new_footprint = 
        (* Hongseok's comment: Not sure whether using predicate_fault
         * below causes a problem of soundness. On the other hand, if
         * we use predicate_warning, we are safe. *)
        if predicate_fault then footprint_normalize footprint
	else footprint_normalize {footprint with foot_pi = a' :: footprint.foot_pi}  
      in 
        (if predicate_fault then E.err "@.@.WARNING: dropping non-footprint %a@.@." pp_atom a'
	  else if predicate_warning then E.err "@.@.WARNING: adding non-footprint %a@.@." pp_atom a');
        {p' with footprint = Some new_footprint}
    else 
      p'
      
(** Conjoin [exp1]=[exp2] with a symbolic heap [prop]. *)
let conjoin_eq ?(footprint=false) exp1 exp2 prop =
  prop_atom_and ~footprint:footprint prop (Aeq(exp1,exp2))

(** Conjoin [exp1!=exp2] with a symbolic heap [prop]. *)
let conjoin_neq ?(footprint=false) exp1 exp2 prop =
  prop_atom_and ~footprint:footprint prop (Aneq (exp1,exp2))

(** Return the equalities in the proposition *)
let prop_get_equalities (p:prop) =
  let eq1 = List.map (fun (i,e) -> (Var i,e)) (sub_to_list p.sub) in
  let pieq = List.filter (function Aeq _ -> true | _ -> false) p.pi in
  let eq2 = List.map (function Aeq(e1,e2) -> e1,e2 | _ -> assert false) pieq
  in eq1 @ eq2

(** Return the sub part of [prop]. *)
let prop_get_sub (p:prop) : subst = p.sub

(** Replace the sub part of [prop]. *)
let prop_replace_sub sub p = 
  let nsub = sub_normalize sub in
  {p with sub = nsub}

(** Return the pi part of [prop]. *)
let prop_get_pi (p:prop) : atom list = p.pi

(** Return the pure part of [prop]. *)
let prop_get_pure (p:prop) : atom list =
  List.map (fun (id1,e2) -> Aeq (Var id1,e2)) (sub_to_list p.sub) @ p.pi


(** Replace the pi part of [prop]. *)
let prop_replace_pi pi p = 
  let npi = pi_normalize p.sub pi 
  in {p with pi = npi}

(** Remove equalities of the form fp=exp for footprint vars fp. *)
let prop_abs_pi_footprint_vars p =
  let filter id = not (ident_is_footprint id)
  in {p with sub = sub_filter filter p.sub}


(** Return the spatial part *)
let prop_get_sigma (p:prop) : hpred list = p.sigma

(** Replace the sigma part of [prop] *)
let prop_replace_sigma sigma p =
  let nsigma = sigma_normalize p.sub sigma
  in {p with sigma = nsigma}

(** Convert a sigma into a prop *)
let prop_of_sigma (sigma : hpred list) : prop =
  {sub = sub_empty;
   pi = [];
   sigma = sigma_normalize sub_empty sigma;
   footprint = None}

(** Create a [prop] without any normalization *)
let prop_create_verbatim pi sigma =
  {sub = sub_empty;
   pi = pi;
   sigma = sigma;
   footprint = None}

(** Allocate one global variable *)
let prop_init_global gvar typ prop : prop =
  let ptsto = mk_ptsto_lvar (gvar, typ, None) in
  prop_hpred_star prop ptsto 

(** Remove seed vars from a prop *)
let prop_remove_seed_vars prop =
  let hpred_not_seed = function
    |  Hpointsto(Lvar pv,_,_) -> not (pvar_is_seed pv)
    | _ -> true in
  let sigma = prop_get_sigma prop in
  let sigma' = List.filter hpred_not_seed sigma
  in prop_replace_sigma sigma' prop

let create_seed_vars sigma =
  let sigma_seed = ref [] in
  let hpred_add_seed = function
    | Hpointsto (Lvar pv,se,typ) ->
	sigma_seed := Hpointsto(Lvar (pvar_to_seed pv),se,typ) :: !sigma_seed
    | _ -> () in
  let () = List.iter hpred_add_seed sigma
  in !sigma_seed

(** Initialize proposition for execution given formal and global
    parameters. The footprint is initialized according to the
    execution mode. *)
let prop_init_formals_locals_seed formals locals prop : prop =
  let normalize_param (id,typ,expo) = match expo with
    | None -> (id,typ,expo)
    | Some e -> (id,typ,Some (exp_normalize_prop prop e)) in
  let locals_norm = List.map normalize_param locals in
  let formals_norm = List.map normalize_param formals in
  let sigma_formals = List.map mk_ptsto_lvar formals_norm in
  let sigma_seed =
    if !Config.footprint_analysis && !Config.footprint
    then create_seed_vars sigma_formals
    else if !Config.footprint_analysis && not !Config.footprint
    then create_seed_vars prop.sigma (* formals already there in re-exe *)
    else [] in
  let sigma_locals =
    let fp_mode = !Config.footprint in
    let () = Config.footprint := false in (* no footprint vars for locals *)
    let sigma_locals = List.map mk_ptsto_lvar locals_norm in
    let () = Config.footprint := fp_mode
    in sigma_locals in
  let sigma = sigma_seed @ sigma_formals @ sigma_locals in
  let footprint =
    if !Config.footprint
    then Some
      {foot_pi = [];
       foot_sigma = sigma_formals}
    else None
  in
    {(prop_sigma_star prop sigma) with
      footprint = footprint}

(** Deallocate the stack variables in list_var  *)
let prop_dispose_stack_proc p list_var =
  let filter = function
    | Hpointsto (Lvar v, _, _) ->
	List.exists (pvar_equal v) list_var
    | _ -> false in
  let sigma_stack,sigma_other = List.partition filter p.sigma in
  let exp_replace = List.map (function
    | Hpointsto (Lvar v, _, _) -> (Lvar v, Var (create_fresh_primed_ident (pvar_get_name v)))
    | _ -> assert false) sigma_stack in
  let pi1 = List.map (fun (id,e) -> Aeq (Var id,e)) (sub_to_list p.sub) in
  let pi = List.map (atom_replace_exp exp_replace) (p.pi @ pi1) in
  let p' =
    {p with sub = sub_empty; pi = []; sigma = sigma_replace_exp exp_replace sigma_other}
  in List.fold_left prop_atom_and p' pi


(** {1 Functions for transforming footprints into propositions.} *)

(** The ones used for abstraction add/remove local stacks in order to
    stop the firing of some abstraction rules. The other usual 
    transforation functions do not use this hack. *)

let get_local_stack cur_sigma init_sigma = 
  let filter_stack = function
    | Hpointsto (Lvar _, _, _) -> true
    | Hpointsto _ | Hlseg _ | Hdllseg _-> false in
  let get_stack_var = function
    | Hpointsto (Lvar pvar, _, _) -> pvar
    | Hpointsto _ | Hlseg _ | Hdllseg _ -> assert false in
  let filter_local_stack old_pvars = function
    | Hpointsto (Lvar pvar, _, _) -> not (List.exists (pvar_equal pvar) old_pvars)
    | Hpointsto _ | Hlseg _ | Hdllseg _ -> false in 
  let init_stack = List.filter filter_stack init_sigma in
  let init_stack_pvars = List.map get_stack_var init_stack in
  let cur_local_stack = List.filter (filter_local_stack init_stack_pvars) cur_sigma in
  let cur_local_stack_pvars = List.map get_stack_var cur_local_stack  
  in (cur_local_stack, cur_local_stack_pvars)

(** Extract the footprint, add a local stack and return it as a prop *)
let prop_extract_footprint_for_abs p = match p.footprint with
  | None -> (prop_emp, [])
  | Some footprint ->
      let (local_stack, local_stack_pvars) = get_local_stack p.sigma footprint.foot_sigma in
      let p0 =
	{sub = sub_empty;
	 pi = [];
	 sigma = sigma_normalize sub_empty (local_stack @ footprint.foot_sigma);
	 footprint=None} in
      let prop = List.fold_left prop_atom_and p0 footprint.foot_pi 
      in (prop, local_stack_pvars)

let remove_local_stack sigma pvars = 
  let filter_non_stack = function
    | Hpointsto (Lvar pvar, _, _) -> not (List.exists (pvar_equal pvar) pvars)
    | Hpointsto _ | Hlseg _ | Hdllseg _ -> true 
  in List.filter filter_non_stack sigma

(** [prop_set_fooprint p p_foot] removes a local stack from [p_foot],
    and sets proposition [p_foot] as footprint of [p]. *)
let prop_set_footprint_for_abs p p_foot local_stack_pvars =
  match p.footprint with
    | None -> p
    | Some fp ->
	let pi = (List.map (fun (i,e) -> Aeq(Var i,e)) (sub_to_list p_foot.sub)) @ p_foot.pi in
	let sigma = remove_local_stack p_foot.sigma local_stack_pvars in
	let footprint = footprint_normalize {foot_pi = pi; foot_sigma = sigma}  
	in {p with footprint = Some footprint}

(** [prop_copy_footprint p1 p2] copies the footprint and pure part of [p1] into [p2] *)
let prop_copy_footprint_pure p1 p2 =
  let pi = prop_get_pure p1
  in List.fold_left prop_atom_and {p2 with footprint = p1.footprint} pi

(** Extract the footprint and return it as a prop *)
let prop_extract_footprint p = match p.footprint with
  | None -> prop_emp
  | Some footprint ->
      let p0 =
	{sub=sub_empty;
	 pi=[];
	 sigma=sigma_normalize sub_empty footprint.foot_sigma;
	 footprint=None} in
      let prop = List.fold_left prop_atom_and p0 footprint.foot_pi 
      in prop

(** Extract the (footprint,current) pair *)
let prop_extract_spec p =
  let pre = prop_extract_footprint p in
  let post = {p with footprint = None}
  in (pre,post)

(** [prop_set_fooprint p p_foot] sets proposition [p_foot] as footprint of [p]. *)
let prop_set_footprint p p_foot =
  match p.footprint with
    | None -> p
    | Some fp ->
	let pi = (List.map (fun (i,e) -> Aeq(Var i,e)) (sub_to_list p_foot.sub)) @ p_foot.pi in
	let footprint = footprint_normalize {foot_pi = pi; foot_sigma = p_foot.sigma} 
	in {p with footprint = Some footprint}


(** Strengthen the footprint by adding pure facts from the current part *)
let prop_strengthen_footprint (p:prop) : prop =
  let is_footprint_atom a =
    let a_fav = atom_fav a
    in fav_for_all a_fav ident_is_footprint
  in match p.footprint with
    | Some footprint ->
	let pure = prop_get_pure p in
	let new_footprint_atoms = List.filter is_footprint_atom pure in
	  if new_footprint_atoms!=[]
	  then (** add pure fact to footprint *)
	    let footprint' = {footprint with foot_pi = footprint.foot_pi @ new_footprint_atoms}
	    in {p with footprint = Some (footprint_normalize footprint')}
	  else p
    | None -> p

exception CANNOT_ADD_FOOTPRINT

(** [prop_footprint_add_pi_sigma_starfld_sigma prop pi sigma missing_fld] extends the footprint of [prop] with [pi,sigma] and extends the fielsd of |-> with [missing_fld] *)
let prop_footprint_add_pi_sigma_starfld_sigma prop pi sigma missing_fld =
  let extend_sigma current_sigma new_sigma =
    let fav = sigma_fav new_sigma in 
      if fav_exists fav (fun id -> not (ident_is_footprint id))
      then raise CANNOT_ADD_FOOTPRINT
      else new_sigma @ current_sigma
  in match prop.footprint with
    | None -> assert false
    | Some footprint ->
	try
	  let footprint' = footprint_normalize
	    {foot_pi = pi @ footprint.foot_pi;
	     foot_sigma = sigma_star_fld (extend_sigma footprint.foot_sigma sigma) missing_fld} in
	  let prop' = {prop with footprint = Some footprint'} in
	  let prop'' = List.fold_right (fun eq p -> prop_atom_and p eq) pi prop'
	  in Some prop''
	with
	  | CANNOT_ADD_FOOTPRINT -> None

(** {2 Functions for renaming primed variables by "canonical names"} *)      

module ExpStack : sig
  val init : exp list -> unit
  val final : unit -> unit
  val is_empty : unit -> bool
  val push : exp -> unit
  val pop : unit -> exp
end = struct
  let stack = Stack.create ()
  let init es = 
    Stack.clear stack;
    List.iter (fun e -> Stack.push e stack) (List.rev es)
  let final () = Stack.clear stack
  let is_empty () = Stack.is_empty stack
  let push e = Stack.push e stack
  let pop () = Stack.pop stack
end

let sigma_get_start_lexps_sort sigma = 
  let exp_compare_neg e1 e2 = - (exp_compare e1 e2) in
  let filter e = fav_for_all (exp_fav e) ident_is_normal  in
  let lexps = sigma_get_lexps filter sigma in 
  List.sort exp_compare_neg lexps 

let rec list_rev_base base = function
  | [] -> base
  | x::xs -> list_rev_base (x::base) xs

let sigma_dfs_sort sigma =
 
  let init () =
    let start_lexps = sigma_get_start_lexps_sort sigma in
    ExpStack.init start_lexps in

  let final () = ExpStack.final () in
  
  let rec handle_strexp = function
    | Eexp e -> ExpStack.push e 
    | Estruct fld_se_list ->
        List.iter (fun (_,se) -> handle_strexp se) fld_se_list 
    | Earray (_, idx_se_list) -> 
        List.iter (fun (_,se) -> handle_strexp se) idx_se_list in

  let rec handle_e visited seen e = function
    | [] -> (visited, List.rev seen)
    | hpred :: cur ->
      begin
        match hpred with 
        | Hpointsto (e', se, _) when exp_equal e e' ->
            handle_strexp se; 
            (hpred::visited, list_rev_base cur seen)
        | Hlseg (_, _, root, next, shared) when exp_equal e root ->
            List.iter ExpStack.push (next::shared);
            (hpred::visited, list_rev_base cur seen)
        | Hdllseg (_, _, iF, oB, oF, iB, shared) 
            when exp_equal e iF || exp_equal e iB ->
            List.iter ExpStack.push (oB::oF::shared);
            (hpred::visited, list_rev_base cur seen)
        | _ ->
            handle_e visited (hpred::seen) e cur
      end in
  
  let rec handle_sigma visited = function
    | [] -> List.rev visited
    | cur ->
        if ExpStack.is_empty () then 
          let cur' = sigma_normalize sub_empty cur in
          list_rev_base cur' visited
        else
          let e = ExpStack.pop () in
          let (visited', cur') = handle_e visited [] e cur in
          handle_sigma visited' cur' in
 
  init (); 
  let sigma' = handle_sigma [] sigma in
  final ();
  sigma'

let prop_dfs_sort p =
  let sigma = prop_get_sigma p in
  let sigma' = sigma_dfs_sort sigma in
  let p' = {p with sigma=sigma'} in
  (* E.stderr "@[<2>P SORTED:@\n%a@\n@." pp_prop p'; *)
  p'

let rec pp_ren f = function 
  | [] -> ()
  | [(i,x)] -> F.fprintf f "%a->%a" pp_ident i pp_ident x
  | (i,x)::ren -> F.fprintf f "%a->%a, %a" pp_ident i pp_ident x pp_ren ren  


let compute_renaming fav =
  let ids = fav_to_list_stable fav in
  let ids_primed, ids_nonprimed = List.partition ident_is_primed ids in
  let ids_footprint = List.filter ident_is_footprint ids_nonprimed in

  let id_base_primed = create_primed_ident name_siltmp 0 in
  let id_base_footprint = create_footprint_ident name_siltmp 0 in

  let rec f id_base index ren_subst = function
    | [] -> ren_subst
    | id::ids -> 
        let new_id = ident_set_stamp id_base index in
        if ident_equal id new_id then 
          f id_base (index+1) ren_subst ids 
        else
          f id_base (index+1) ((id,new_id)::ren_subst) ids in

  let ren_primed = f id_base_primed 0 [] ids_primed in
  let ren_footprint = f id_base_footprint 0 [] ids_footprint in

  ren_primed @ ren_footprint

let rec idlist_assoc id = function
  | [] -> raise Not_found
  | (i,x)::l -> if ident_equal i id then x else idlist_assoc id l

let ident_captured_ren ren id = 
  try (idlist_assoc id ren) 
  with Not_found -> id 
  (* If not defined in ren, id should be mapped to itself *)

let rec exp_captured_ren ren = function 
  | Var id -> Var (ident_captured_ren ren id)
  | Const_int n as e -> e
  | Const_fun fn as e -> e
  | Sizeof t as e -> e
  | Cast (t, e) -> Cast (t, exp_captured_ren ren e) 
  | UnOp (op, e) -> UnOp (op, exp_captured_ren ren e)
  | BinOp (op, e1, e2) -> 
      let e1' = exp_captured_ren ren e1 in
      let e2' = exp_captured_ren ren e2 
      in BinOp (op, e1', e2')
  | Lvar id -> Lvar id
  | Lfield (e, fld) -> Lfield (exp_captured_ren ren e, fld)
  | Lindex (e1, e2) ->
      let e1' = exp_captured_ren ren e1 in
      let e2' = exp_captured_ren ren e2
      in Lindex(e1', e2')

let rec strexp_captured_ren ren = function
  | Eexp e -> 
      Eexp (exp_captured_ren ren e)
  | Estruct fld_se_list ->
      let f (fld,se) = (fld, strexp_captured_ren ren se) 
      in Estruct (List.map f fld_se_list)
  | Earray (size, idx_se_list) ->
      let f (idx,se) = (exp_captured_ren ren idx, strexp_captured_ren ren se)
      in Earray (size, List.map f idx_se_list)

let atom_captured_ren ren = function
  | Aeq (e1,e2) ->
      Aeq (exp_captured_ren ren e1, exp_captured_ren ren e2)
  | Aneq (e1,e2) ->
      Aneq (exp_captured_ren ren e1, exp_captured_ren ren e2)

let rec hpred_captured_ren ren = function
  | Hpointsto (base, se, te) ->
      let base' = exp_captured_ren ren base in
      let se' = strexp_captured_ren ren se in
      let te' = exp_captured_ren ren te 
      in Hpointsto (base', se', te')
  | Hlseg (k,para, e1, e2, elist) ->
      let para' = hpara_ren para in
      let e1' = exp_captured_ren ren e1 in
      let e2' = exp_captured_ren ren e2 in
      let elist' = List.map (exp_captured_ren ren) elist
      in Hlseg (k,para',e1',e2',elist')
  | Hdllseg (k,para,e1,e2,e3,e4,elist) ->
      let para' = hpara_dll_ren para in
      let e1' = exp_captured_ren ren e1 in
      let e2' = exp_captured_ren ren e2 in
      let e3' = exp_captured_ren ren e3 in
      let e4' = exp_captured_ren ren e4 in
      let elist' = List.map (exp_captured_ren ren) elist
      in Hdllseg (k,para',e1',e2',e3',e4',elist')
	
and hpara_ren para =
  let av = hpara_shallow_av para in
  let ren = compute_renaming av in
  let root' = ident_captured_ren ren para.root in
  let next' = ident_captured_ren ren para.next in
  let svars' = List.map (ident_captured_ren ren) para.svars in
  let evars' = List.map (ident_captured_ren ren) para.evars in
  let body' = List.map (hpred_captured_ren ren) para.body 
  in {root=root'; next=next'; svars=svars'; evars=evars'; body=body'}

and hpara_dll_ren para =
  let av = hpara_dll_shallow_av para in
  let ren = compute_renaming av in
  let iF = ident_captured_ren ren para.cell in
  let oF = ident_captured_ren ren para.flink in
  let oB = ident_captured_ren ren para.blink in
  let svars' = List.map (ident_captured_ren ren) para.svars_dll in
  let evars' = List.map (ident_captured_ren ren) para.evars_dll in
  let body' = List.map (hpred_captured_ren ren) para.body_dll 
  in {cell=iF; flink=oF; blink=oB; svars_dll=svars'; evars_dll=evars'; body_dll=body'}

let fav_captured_ren ren fav =
  let fav_lst = fav_to_list fav in
  let fav_lst' = List.map (ident_captured_ren ren) fav_lst 
  in fav_from_list fav_lst'

let pi_captured_ren ren pi = 
  List.map (atom_captured_ren ren) pi

let sigma_captured_ren ren sigma = 
  List.map (hpred_captured_ren ren) sigma

let footprint_captured_ren ren (footprint: footprint option) = match footprint with
  | None -> None
  | Some footprint ->
      Some
	{foot_pi = pi_captured_ren ren footprint.foot_pi;
	 foot_sigma = sigma_captured_ren ren footprint.foot_sigma}

let sub_captured_ren ren sub =
  sub_map (ident_captured_ren ren) (exp_captured_ren ren) sub 

(** Canonicalize the names of primed variables and footprint vars. *)
let prop_rename_primed_footprint_vars p = 
  let bound_vars = 
    let filter id = ident_is_footprint id || ident_is_primed id in 
    let p_dfs = prop_dfs_sort p in
    let fvars_in_p = prop_fav p_dfs 
    in fav_filter_ident fvars_in_p filter;
      fvars_in_p in
  let ren = compute_renaming bound_vars in
  let sub' = sub_captured_ren ren p.sub in
  let pi' = pi_captured_ren ren p.pi in
  let sigma' = sigma_captured_ren ren p.sigma in
  let footprint' = footprint_captured_ren ren p.footprint in
  let sub_for_normalize = sub_empty in 
    (* It is fine to use the empty substituion during normalization 
       because the renaming maintains that a substitution is normalized *)
  let nsub' = sub_normalize sub' in
  let npi' = pi_normalize sub_for_normalize pi' in
  let nsigma' = sigma_normalize sub_for_normalize sigma' in
  let nfootprint' = match footprint' with
    | None -> None
    | Some fp' -> Some (footprint_normalize fp') in
  let p' = {sub=nsub';pi=npi';sigma=nsigma'; footprint=nfootprint'} in
  (*
  E.log "@[<2>BEFORE RENAMING:@\n";
  E.log "%a@\n@." pp_prop p;
  E.log "@[<2>AFTER RENAMING:@\n";
  E.log "%a@\n@." pp_prop p';
  E.log "@[<2>RENAMING:@\n";
  E.log "%a@\n@." pp_ren ren;
  *)
  p'


(*
let prop_rename_primed_footprint_vars p =
  let p' = prop_rename_primed_footprint_vars p in
  let () = E.stderr "@.BEFORE RENAMING:@.%a@.AFTER RENAMING:@.%a@." pp_prop p pp_prop p'
  in p'
*)

(** {2 Functionss for changing and generating propositions} *)

let mem_idlist i l =
  List.exists (fun id -> ident_equal i id) l

let id_exp_compare (id1,e1) (id2,e2) =
  let n = exp_compare e1 e2
  in if n <> 0 then n
    else ident_compare id1 id2 

let saturate sub idel =
  let idel' = List.sort id_exp_compare idel in
  let epairs = List.map (fun (i1,e2) -> (exp_sub sub (Var i1), e2)) idel' in 
  let eqs = List.map (fun (e1,e2) -> Aeq(e1, e2)) epairs in
  let rec f acc = function
    | [] | [_] -> acc
    | (e1,e1')::(e2,e2')::epairs' ->
        if exp_equal e1' e2' then f (Aeq(e1,e2)::acc) ((e2,e2')::epairs')
        else f acc ((e2,e2')::epairs')
  in f eqs epairs

(** Apply renaming substitution to a proposition. *)
let prop_ren_sub (ren_sub:subst) (prop:prop) =
  let sub' = sub_range_map (exp_sub ren_sub) prop.sub in
  let (sub_change,sub_keep) =
    let filter = function
      | Var i -> ident_is_primed i (** need to change x=y if y becomes _y *)
      | _ -> false
    in sub_range_partition filter sub' in
  let prop' = 
    let pi' = pi_sub ren_sub prop.pi in
    let npi' = pi_normalize sub_keep pi' in
    let sigma' = sigma_sub ren_sub prop.sigma in
    let nsigma' = sigma_normalize sub_keep sigma' in
    let nfootprint' = match prop.footprint with
      | None -> None
      | Some footprint ->
	  let footprint' = 
            {foot_pi = pi_sub ren_sub footprint.foot_pi; 
             foot_sigma = sigma_sub ren_sub footprint.foot_sigma}
	  in Some (footprint_normalize footprint')
    in {sub=sub_keep;pi=npi';sigma=nsigma';footprint=nfootprint'} in
(*
  let res_prop =
    let add (i1,e) p = match e with
      | Var i2 -> prop_atom_and p (Aeq (exp_sub ren_sub (Var i1), e))
      | _ -> assert false
    in List.fold_right add (sub_to_list sub_change) prop' in
*)
  let res_prop' = 
    let eqs = saturate ren_sub (sub_to_list sub_change) 
    in List.fold_right (fun eq p -> prop_atom_and p eq) eqs prop'
  in if (prop_equal prop res_prop') then prop else res_prop'

(** Apply renaming substitution to a proposition without normalizing. *)
let prop_apply_renaming_no_normalize (ren_sub:subst) (prop:prop) : prop =
  let pi = (List.map (fun (i,e) -> Aeq(Var i,e)) (sub_to_list prop.sub)) @ prop.pi in
  let pi' = pi_sub ren_sub pi in
  let sigma' = sigma_sub ren_sub prop.sigma
  in {prop with sub=sub_empty;pi=pi';sigma=sigma'}

(** Existentially quantify the [ids] in [prop]. 
    [ids] should not contain any primed variables. *)
let exist_quantify fav prop =
  let ids = fav_to_list fav in
  if List.exists ident_is_primed ids then assert false; (* sanity check *)

  let gen_fresh_id_sub id = (id, Var (create_fresh_primed_ident name_siltmp)) in  
  let ren_sub = sub_of_list (List.map gen_fresh_id_sub ids) in
  let prop' =
    let sub = sub_filter (fun i -> not (mem_idlist i ids)) prop.sub (** throw away x=E if x becomes _x *)
    in if sub_equal sub prop.sub then prop
      else {prop with sub=sub}
  in 
     (*
     E.log "@[<2>.... Existential Quantification ....\n";
     E.log "SUB:%a\n" pp_sub prop'.sub;
     E.log "PI:%a\n" pp_pi prop'.pi;
     E.log "PROP:%a\n@." pp_prop prop';
     *)
     prop_ren_sub ren_sub prop'

(** Apply subsitution to prop. Result is normalized. *)
let prop_sub subst prop =
  let pi = prop.pi @ List.map (fun (x,e) -> Aeq (Var x, e)) (sub_to_list prop.sub) in
  let pi' = pi_sub subst pi in
  let sigma' = sigma_sub subst prop.sigma in
  let p0 =
    {sub=sub_empty;
     pi=[];
     sigma=sigma';
     footprint=None}
  in List.fold_left prop_atom_and p0 pi'

(** Change exps in prop by [f] *)
let prop_expmap (f:exp->exp) prop =
  let pi = List.map (atom_expmap f) prop.pi in
  let sigma = List.map (hpred_expmap f) prop.sigma in
  let footprint = match prop.footprint with
    | None -> None
    | Some fp ->
	let foot_pi = List.map (atom_expmap f) fp.foot_pi in
	let foot_sigma = List.map (hpred_expmap f) fp.foot_sigma
	in Some {foot_pi=foot_pi;foot_sigma=foot_sigma}
  in {prop with pi=pi;sigma=sigma;footprint=footprint}

(** convert identifiers in fav to kind [k] *)
let vars_make_unprimed fav prop =
  let ids = fav_to_list fav in
  let ren_sub = sub_of_list (List.map (fun i -> (i, Var (create_fresh_normal_ident (ident_name i)))) ids)
  in prop_ren_sub ren_sub prop

(** convert the normal vars to primed vars. *)
let prop_normal_vars_to_primed_vars p =
  let fav = prop_fav p
  in
    fav_filter_ident fav ident_is_normal;
    exist_quantify fav p

(** convert the primed vars to normal vars. *)
let prop_primed_vars_to_normal_vars p =
  let fav = prop_fav p
  in
    fav_filter_ident fav ident_is_primed;
    vars_make_unprimed fav p

(** Rename all primed variables fresh *)
let prop_rename_primed_fresh p =
  let ids_primed = 
    let fav = prop_fav p in
    let ids = fav_to_list fav 
    in List.filter ident_is_primed ids in
  let ren_sub = 
    let f i = (i, Var (create_fresh_primed_ident name_siltmp (* (ident_name i) *))) 
    in sub_of_list (List.map f ids_primed)
  in prop_ren_sub ren_sub p

(** {2 Prop iterators} *)
(* Hongseok's comment: Many of prop_iter ignores the pit_old part of
 * sigma. For instance, prop_iter_map applies a given function f only to
 * the pit_curr and pit_new. I am slightly worried that this might cause
 * some problems. *)

(** Iterator state over sigma. *)
type 'a prop_iter =
    {pit_sub : subst; (** substitution for equalities *)
     pit_pi : atom list;    (** pure part *)
     pit_old : hpred list; (** sigma already visited *)
     pit_curr : hpred;      (** current element *)
     pit_state : 'a option; (** state of current element *)
     pit_new : hpred list; (** sigma not yet visited *)
     pit_footprint : footprint option; (** Footprint *)
    }

let prop_iter_create prop =
  match prop.sigma with
    | hpred::sigma' -> Some
	{pit_sub = prop.sub;
	 pit_pi = prop.pi;
	 pit_old = [];
	 pit_curr = hpred;
	 pit_state = None;
	 pit_new = sigma';
	 pit_footprint = prop.footprint}
    | _ -> None

(** Return the prop associated to the iterator. *)
let prop_iter_to_prop iter =
  let sigma = List.rev_append iter.pit_old (iter.pit_curr::iter.pit_new) in
  let normalized_sigma = sigma_normalize iter.pit_sub sigma 
  in {sub = iter.pit_sub; pi = iter.pit_pi; sigma = normalized_sigma; footprint=iter.pit_footprint}

(** Remove the current element of the iterator, and return the prop
    associated to the resulting iterator *)
let prop_iter_remove_curr_then_to_prop iter =
  let sigma = List.rev_append iter.pit_old iter.pit_new in
  let normalized_sigma = sigma_normalize iter.pit_sub sigma 
  in {sub = iter.pit_sub;
      pi = iter.pit_pi;
      sigma = normalized_sigma;
      footprint = iter.pit_footprint}

(** Return the current hpred and state. *)
let prop_iter_current iter =
  (iter.pit_curr, iter.pit_state)

(** Update the current element of the iterator. *)
let prop_iter_update_current iter hpred =
 {iter with pit_curr = hpred; pit_state = None}

(** Update the current element of the iterator by a nonempty list of
    elements. *)
let prop_iter_update_current_by_list iter = function
  | [] -> assert false (* the list should be nonempty *)
  | hpred::hpred_list -> 
      let pit_new' = hpred_list@iter.pit_new 
      in {iter with pit_curr=hpred; pit_state=None; pit_new=pit_new'}

let prop_iter_next iter =
  match iter.pit_new with
    | [] -> None
    | hpred'::new' -> Some
	{iter with
	  pit_old = iter.pit_curr::iter.pit_old;
	  pit_curr = hpred';
	  pit_state = None;
	  pit_new = new'}

let prop_iter_remove_curr_then_next iter =
  match iter.pit_new with
    | [] -> None
    | hpred'::new' -> Some
	{iter with
	  pit_old = iter.pit_old;
	  pit_curr = hpred';
	  pit_state = None;
	  pit_new = new'}

let prop_iter_prev_then_insert iter hpred =
  {iter with 
     pit_new = iter.pit_curr::iter.pit_new;
     pit_curr = hpred }


(** Scan sigma to find an [hpred] satisfying the filter function. *)
let rec prop_iter_find iter filter =
  match filter iter.pit_curr with
    | Some st -> Some {iter with pit_state=Some st}
    | None ->
	(match prop_iter_next iter with
	  | None -> None
	  | Some iter' -> prop_iter_find iter' filter)

let fav_max_stamp fav =
  let max_stamp = ref 0 in
  let f id = max_stamp := max !max_stamp (ident_get_stamp id) in
  let () = List.iter f (fav_to_list fav)
  in max_stamp

(* Add a pointsto for [root(lexp):typ] to the iterator and to the
 * footprint, if it's compatible with the allowed footprint
 * variables. This function ensures that [root(lexp):typ] is the
 * current hpred of the iterator.  typ is the type of the root of
 * lexp. *)
let prop_iter_add_hpred_footprint iter (lexp,typ) =
  let footprint = match iter.pit_footprint with
    | None -> assert false
    | Some footprint ->
	let fav_lexp =
	  let fav = exp_fav lexp
	  in
	    fav_filter_ident fav (fun id -> not (ident_is_footprint id));
	    fav
	in 
	  if not (fav_is_empty fav_lexp) then 
            (F.fprintf F.std_formatter "@.@. !!!! Footprint Error, Bad Exp : %a !!!! @.@." pp_exp lexp;
             raise Bad_footprint);
	  footprint in
  let lexp_root = Sil.root_of_lexp lexp in
  let max_stamp = fav_max_stamp (footprint_fav iter.pit_footprint) in
  let ptsto = mk_ptsto_exp_footprint footprint (lexp_root,lexp,typ) max_stamp in
  let () =
    E.d_strln "++++ Adding footprint frame";
    d_prop (prop_hpred_star prop_emp ptsto);
    E.d_ln () in
  let foot_sigma = ptsto :: footprint.foot_sigma in
  let iter' = prop_iter_prev_then_insert iter ptsto 
    (* Hongseok's comment: Is it fine to put the ptsto right before
     * the current hpred of the iterator? *)
  in {iter' with pit_footprint = Some {footprint with foot_sigma=foot_sigma}}

(* Add a pointsto for [root(lexp):typ] to the sigma and footprint of a
 * prop, if it's compatible with the allowed footprint
 * variables. Then, change it into a iterator. This function ensures
 * that [root(lexp):typ] is the current hpred of the iterator.  typ
 * is the type of the root of lexp. *)
let prop_iter_add_hpred_footprint_to_prop prop (lexp,typ) =
  let footprint = match prop.footprint with
    | None -> assert false
    | Some footprint ->
	let fav_lexp =
	  let fav = exp_fav lexp
	  in fav_filter_ident fav (fun id -> not (ident_is_footprint id));
	    fav
	in 
	  if not (fav_is_empty fav_lexp) then 
            (F.fprintf F.std_formatter "@.@. !!!! Footprint Error, Bad Exp : %a !!!! @.@." pp_exp lexp;
             assert false);
	  footprint in
  let lexp_root = Sil.root_of_lexp lexp in
  let max_stamp = fav_max_stamp (footprint_fav prop.footprint) in
  let ptsto = mk_ptsto_exp_footprint footprint (lexp_root,lexp,typ) max_stamp in
  let () =
    E.d_strln "++++ Adding footprint frame";
    d_prop (prop_hpred_star prop_emp ptsto);
    E.d_ln () in
  let foot_sigma = ptsto :: footprint.foot_sigma in
  let footprint_new = footprint_normalize {footprint with foot_sigma = foot_sigma} in
  let prop_new = {prop with footprint = Some footprint_new} 
  in match (prop_iter_create prop_new) with
    | None -> 
	let prop_new' = prop_hpred_star prop_new ptsto 
	in begin  match (prop_iter_create prop_new') with
	  | None -> assert false
	  | Some iter -> iter
	end	    
    | Some iter -> prop_iter_prev_then_insert iter ptsto

(** Set the state of the iterator *)
let prop_iter_set_state iter state =
  {iter with pit_state = Some state}

let prop_iter_make_id_primed id iter =
  let pid = create_fresh_primed_ident (ident_name id) in
  let sub_id = sub_of_list [(id, Var pid)] in

  let normalize (id,e) = 
    let eq' = Aeq(exp_sub sub_id (Var id), exp_sub sub_id e) in
    atom_normalize sub_empty eq' in

  let rec split pairs_unpid pairs_pid  = function 
    | [] -> (List.rev pairs_unpid, List.rev pairs_pid)
    | eq::eqs_cur ->
      begin
        match eq with 
        | Aeq (Var id1, e1) when ident_in_exp id1 e1 -> 
            E.err "@[<2>#### ERROR: an assumption of the analyzer broken ####@\n";
            E.err "Broken Assumption: id notin e for all (id,e) in sub@\n";
            E.err "(id,e) : (%a,%a)@\n" pp_ident id1 pp_exp e1;
            E.err "PROP : %a@\n@." pp_prop (prop_iter_to_prop iter);
            assert false
        | Aeq (Var id1, e1) when ident_equal pid id1 ->  
            split pairs_unpid ((id1,e1)::pairs_pid) eqs_cur
        | Aeq (Var id1, e1) ->
            split ((id1,e1)::pairs_unpid) pairs_pid eqs_cur
        | _ ->
            assert false
      end in

  let rec get_eqs acc = function 
    | [] | [_] -> 
        List.rev acc
    | (_,e1) :: (((_,e2) :: pairs') as pairs) -> 
        get_eqs (Aeq(e1,e2)::acc) pairs in

  let sub_new, sub_use, eqs_add =
    let eqs = List.map normalize (sub_to_list iter.pit_sub) in
    let pairs_unpid, pairs_pid = split [] [] eqs in
    match pairs_pid with
    | [] -> 
        let sub_unpid = sub_of_list pairs_unpid in
        let pairs = (id, Var pid) :: pairs_unpid in
        sub_unpid, sub_of_list pairs, [] 
    | (id1,e1)::_ ->
        let sub_id1 = sub_of_list [(id1,e1)] in
        let pairs_unpid' = 
          List.map (fun (id',e') -> (id', exp_sub sub_id1 e')) pairs_unpid in 
        let sub_unpid = sub_of_list pairs_unpid' in
        let pairs = (id, e1) :: pairs_unpid' in
        sub_unpid, sub_of_list pairs, get_eqs [] pairs_pid in
  let nsub_new = sub_normalize sub_new in 

  { iter with
    pit_sub = nsub_new;
    pit_pi = pi_sub sub_use (iter.pit_pi @ eqs_add);
    pit_old = sigma_sub sub_use iter.pit_old;
    pit_curr = hpred_sub sub_use iter.pit_curr;
    pit_new = sigma_sub sub_use iter.pit_new }

(** Free vars of the iterator except the current hpred (and footprint). *)
let prop_iter_noncurr_fav_add fav iter =
  sub_fav_add fav iter.pit_sub;
  pi_fav_add fav iter.pit_pi;
  sigma_fav_add fav iter.pit_old;
  sigma_fav_add fav iter.pit_new

let prop_iter_noncurr_fav iter =
  fav_imperative_to_functional prop_iter_noncurr_fav_add iter

let unSome = function
  | Some x -> x
  | _ -> assert false

let rec strexp_gc_fields (fav:fav) se = match se with
  | Eexp e -> (match e with
      | Var id ->
	  if fav_mem fav id || !Config.footprint_analysis (* no gc at all in footprint *)
	  then Some se
	  else None
      | _ -> Some se)
  | Estruct fsel ->
      let fselo = List.map (fun (f,se) -> (f,strexp_gc_fields fav se)) fsel in
      let fsel' =
	let fselo' = List.filter (function | (_,Some _) -> true | _ -> false) fselo
	in List.map (function (f,seo) -> (f,unSome seo)) fselo'
      in if fld_strexp_list_compare fsel fsel' = 0 then Some se
	else Some (Estruct fsel')
  | Earray _ -> Some se

let hpred_gc_fields (fav:fav) hpred = match hpred with
  | Hpointsto (e,se,te) ->
      exp_fav_add fav e;
      exp_fav_add fav te;
      (match strexp_gc_fields fav se with
	| None -> hpred
	| Some se' ->
	    if strexp_compare se se' = 0 then hpred
	    else Hpointsto (e,se',te))
  | Hlseg _ | Hdllseg _ -> 
      (* Hongseok's comment: A more aggressive strategy will look at the
       * definition of para in Hlseg or Hdllseg, and reduce the strexp's in
       * the para. I am slightly afraid of doing that, since it might cause
       * the analyzer to diverge. *)
      hpred
	

let rec prop_iter_map f iter =
  let hpred_curr = f iter in
  let iter' = {iter with pit_curr = hpred_curr} 
  in match prop_iter_next iter' with
    | None -> iter'
    | Some iter'' -> prop_iter_map f iter''

(** Collect garbage fields. *)
let prop_iter_gc_fields iter =
  let f iter' =
    let fav = prop_iter_noncurr_fav iter'
    in hpred_gc_fields fav iter'.pit_curr
  in prop_iter_map f iter

let prop_case_split prop = 
  let pi_sigma_list = sigma_to_sigma_ne prop.sigma in
  let f props_acc (pi, sigma) =
    let sigma' = sigma_normalize_prop prop sigma in
    let prop' = { prop with sigma = sigma' }
    in (List.fold_left prop_atom_and prop' pi)::props_acc
  in List.fold_left f [] pi_sigma_list   

(** Raise an exception if the prop is not normalized *)
let check_prop_normalized prop =
  let sigma' = sigma_normalize_prop prop prop.sigma
  in if sigma_equal prop.sigma sigma' == false then assert false

let prop_expand prop =
(*
  let _ = check_prop_normalized prop in
*)
  let prop_list = prop_case_split prop
  in List.map prop_rename_primed_footprint_vars prop_list

(*** START of module Metrics ***)
module Metrics : sig
  val prop_size : prop -> int
  val prop_chain_size : prop -> int
end = struct
  let ptsto_weight = 1
  and lseg_weight = 3
  and pi_weight = 1

  let rec hpara_size hpara = sigma_size hpara.body

  and hpara_dll_size hpara_dll = sigma_size hpara_dll.body_dll

  and hpred_size = function
    | Hpointsto _ -> ptsto_weight
    | Hlseg (_,hpara,_,_,_) -> lseg_weight * hpara_size hpara
    | Hdllseg (_,hpara_dll,_,_,_,_,_) -> lseg_weight * hpara_dll_size hpara_dll

  and sigma_size sigma = 
    let size = ref 0
    in List.iter (fun hpred -> size := hpred_size hpred + !size) sigma; !size

  let pi_size pi = pi_weight * List.length pi

  module ExpMap =
    Map.Make (struct
      type t = exp
      let compare = exp_compare end)

  (** Approximate the size of the longest chain by counting the max
      number of |-> with the same type and whose lhs is primed or
      footprint *)
  let sigma_chain_size sigma =
    let tbl = ref ExpMap.empty in
    let add t =
      try
	let count = ExpMap.find t !tbl
	in tbl := ExpMap.add t (count+1) !tbl
      with
	| Not_found ->
	    tbl := ExpMap.add t 1 !tbl in
    let process_hpred = function
      | Hpointsto (e,_,te) ->
	  (match e with
	    | Var id when ident_is_primed id || ident_is_footprint id -> add te
	    | _ -> ())
      | Hlseg _ | Hdllseg _ -> () in
    let () = List.iter process_hpred sigma in
    let size = ref 0 in
    let () = ExpMap.iter (fun t n -> size := max n !size) !tbl
    in !size

  (** Compute a size value for the prop, which indicates its
      complexity *)
  let prop_size p =
    let size_current = sigma_size p.sigma in
    let size_footprint =  match p.footprint with
      | None -> 0
      | Some fp -> sigma_size fp.foot_sigma
    in max size_current size_footprint

  (** Approximate the size of the longest chain by counting the max
      number of |-> with the same type and whose lhs is primed or
      footprint *)
  let prop_chain_size p =
    let fp_size = match p.footprint with
      | None -> 0
      | Some fp -> pi_size fp.foot_pi + sigma_size fp.foot_sigma
    in pi_size p.pi + sigma_size p.sigma + fp_size
end
(*** END of module Metrics ***)

(* Turn an expression representing a type into the type it represents *)
let texp_to_typ = function
  | Sizeof t -> t
  | t ->
      E.stderr "Cannot covert text to typ: %a@." pp_exp t;
      assert false

(** [prop_iter_extend_ptsto iter lexp] extends the current psto
    predicate in [iter] with enough fields to follow the path in
    [lexp] -- field splitting model *)
let prop_iter_extend_ptsto iter lexp =
  (*  E.stderr "@.Extending %a in@.%a@." pp_exp lexp  pp_prop (prop_iter_to_prop iter); *)
  let offset = (collect_offset lexp) in
  let max_stamp = fav_max_stamp (footprint_fav iter.pit_footprint) in
  let max_stamp_val = !max_stamp in
  let extend_footprint_pred = function
    | Hpointsto(e,se,te) ->
	let t = texp_to_typ te in
	let se' = strexp_extend_values kfootprint (ref max_stamp_val) se t offset
	in Hpointsto (e,se',te)
    | Hlseg (k,hpara,e1,e2,el) ->
	(match hpara.body with
	  | Hpointsto(e',se',te')::body_rest ->
	      let t' = texp_to_typ te' in
	      let se'' = strexp_extend_values kfootprint (ref max_stamp_val) se' t' offset in
	      let body' = Hpointsto(e',se'',te')::body_rest in
	      let hpara' = {hpara with body=body'}
	      in Hlseg(k,hpara',e1,e2,el)
	  | _ -> assert false)
    | _ -> assert false in
  let do_extend e se t =
    match e with
      | Var id when ident_is_footprint id ->
	  let se' = strexp_extend_values kfootprint max_stamp se t offset in
	  let fp = match iter.pit_footprint with Some fp -> fp | None -> assert false in
	  let sigma_pto,sigma_rest =
	    List.partition (function
	      | Hpointsto(e',_,_) -> exp_equal e e'
	      | Hlseg (_,_,e1,e2,_) -> exp_equal e e1
	      | Hdllseg (_,_,e_iF,e_oB,e_oF,e_iB,_) -> exp_equal e e_iF || exp_equal e e_iB
	    ) fp.foot_sigma in
	  let sigma' = match sigma_pto with
	    | [hpred] -> (extend_footprint_pred hpred)::sigma_rest
	    | _ ->
		E.err "@.WARNING: Cannot extend %a in@.%a@." pp_exp lexp pp_prop (prop_iter_to_prop iter);
		fp.foot_sigma in
	  let fp' =
	    let fp_sigma = List.stable_sort hpred_compare sigma'
	    in {fp with foot_sigma = fp_sigma} in
	  let iter' =
	    {iter with pit_curr = Hpointsto (e,se',Sizeof t); pit_footprint = Some fp'}
	  in
	    (*
	      E.err "@.@.iter before:@.%a@." pp_prop (prop_iter_to_prop iter);
	      E.err "@.@.iter after:@.%a@." pp_prop (prop_iter_to_prop iter');
	    *)
	    iter'
      | Var _ -> iter
      | Lvar _ -> iter
      | Lfield _ -> assert false
      | Const_int _ -> iter
      | _ ->
	  assert false
  in match offset with
    | [] -> iter
    | _::_ ->
	let (e,se,te) = match prop_iter_current iter with
	  | Hpointsto (e,se,te),_ -> (e,se,te)
	  | _ -> assert false
	in do_extend e se (texp_to_typ te)

(** Check if the path in exp exists already in the current ptsto predicate *)
let prop_iter_check_fields_ptsto iter lexp =
  let offset = (collect_offset lexp) in
  let (e,se,t) = match prop_iter_current iter with
    | Hpointsto (e,se,t),_ -> (e,se,t)
    | _ -> assert false in
  let rec check_offset se off = match off with
    | [] -> true
    | fld::off' ->
	(match se with
	  | Estruct fsel ->
	      (try
		  let (_,se') = List.find (function (fld',_) -> fld_equal fld fld') fsel
		  in check_offset se' off'
		with Not_found -> false)
	  | _ -> false)
  in check_offset se offset

let rec create_struct_all_values kind max_stamp t : strexp = match t with
  | Tstruct ftl ->
      let go (f,t) = (f, create_struct_all_values kind max_stamp t)
      in Estruct (List.map go (sort_ftl ftl))
  | Tarray (t,n) -> Earray (n,[])
  | Tint | Tfloat | Tvoid  | Tfun | Tptr _ -> 
      incr max_stamp;
      let id = create_ident kind name_siltmp !max_stamp
      in Eexp (Var id)
  | Tvar _ -> assert false

let rec struct_extend_all_values kind max_stamp fsel ftl = match fsel,ftl with
  | [],[] -> []
  | _::_,[] -> assert false
  | (f,se)::fsel',(f1,t)::ftl' ->
      (match name_compare f f1 with
	| 0 -> (f,se)::struct_extend_all_values kind max_stamp fsel' ftl'
	| n when n>0 ->
	    let se' = create_struct_all_values kind max_stamp t
	    in (f1,se') :: struct_extend_all_values kind max_stamp fsel ftl' 
	| _ -> assert false)
  | [],(f1,t)::ftl' ->
      let se' = create_struct_all_values kind max_stamp t
      in (f1,se') :: struct_extend_all_values kind max_stamp fsel ftl'

let strexp_extend_all_structs kind max_stamp se t = match se,t with
  | Eexp e, _ -> se
  | Estruct fsel, Tstruct ftl ->
      let fsel' =
	struct_extend_all_values kind max_stamp fsel (sort_ftl ftl)
      in Estruct fsel'
  | Earray _, Tarray _ -> se
  | _ -> assert false

let hpred_extend_all_structs kind max_stamp hpred : hpred = match hpred with
  | Hpointsto (e,se,te) ->
      let se' =
	strexp_extend_all_structs kind max_stamp se (texp_to_typ te)
      in Hpointsto (e,se',te)
  | _ -> hpred

(** Extend all the structs in [prop] with fresh variables *)
let prop_extend_all_structs kind prop : prop =
  let max_stamp = fav_max_stamp (prop_fav prop) in
  let sigma = List.map (hpred_extend_all_structs kind max_stamp) prop.sigma in
  let nsigma = sigma_normalize prop.sub sigma
  in {prop with sigma = nsigma}


let rec sexp_names_add ns = function
  | Eexp e -> exp_names_add ns e
  | Estruct fsel ->
      let go (f,se) =
	NameSet.add ns f;
	sexp_names_add ns se	
      in List.iter go fsel
  | Earray (n,esel) ->
      let go (e,se) =
	exp_names_add ns e;
	sexp_names_add ns se
      in List.iter go esel

let rec sexp_names_update (ne:NameEnv.t) = function
  | Eexp e ->
      let e' = exp_names_update ne e
      in Eexp e'
  | Estruct fsel ->
      let go (f,se) = (NameEnv.name_update ne f, sexp_names_update ne se) in
      let fsel' = List.map go fsel
      in Estruct fsel'
  | Earray (n,esel) ->
      let go (e,se) = (exp_names_update ne e, sexp_names_update ne se) in
      let esel' = List.map go esel
      in Earray (n,esel')

let atom_names_add ns = function
  | Aeq (e1,e2) | Aneq (e1,e2) ->
      exp_names_add ns e1;
      exp_names_add ns e2

let atom_names_update ne = function
  | Aeq (e1,e2) ->
      Aeq (exp_names_update ne e1, exp_names_update ne e2)
  | Aneq (e1,e2) ->
      Aneq (exp_names_update ne e1, exp_names_update ne e2)

let pi_names_add ns pi =
  List.iter (atom_names_add ns) pi

let pi_names_update ne pi =
  List.map (atom_names_update ne) pi

let rec hpred_names_add ns = function
  | Hpointsto (e,se,te) ->
      exp_names_add ns e;
      sexp_names_add ns se;
      exp_names_add ns te
  | Hlseg (_,hpara,e1,e2,el) ->
      hpara_names_add ns hpara;
      exp_names_add ns e1;
      exp_names_add ns e2;
      List.iter (exp_names_add ns) el
  | Hdllseg (_,hpara_dll,e1,e2,e3,e4,el) ->
      hpara_dll_names_add ns hpara_dll;
      exp_names_add ns e1;
      exp_names_add ns e2;
      exp_names_add ns e3;
      exp_names_add ns e4;
      List.iter (exp_names_add ns) el

and hpara_names_add ns {root=id1;next=id2;svars=idl1;evars=idl2;body=hpredl} =
  NameSet.add_ident ns id1;
  NameSet.add_ident ns id2;
  List.iter (NameSet.add_ident ns) idl1;
  List.iter (NameSet.add_ident ns) idl2;
  List.iter (hpred_names_add ns) hpredl

and hpara_dll_names_add ns {cell=id1;blink=id2;flink=id3;svars_dll=idl1;evars_dll=idl2;body_dll=hpredl} =
  NameSet.add_ident ns id1;
  NameSet.add_ident ns id2;
  NameSet.add_ident ns id3;
  List.iter (NameSet.add_ident ns) idl1;
  List.iter (NameSet.add_ident ns) idl2;
  List.iter (hpred_names_add ns) hpredl

let rec hpred_names_update ne = function
  | Hpointsto (e,se,te) ->
      let e' = exp_names_update ne e in
      let se' = sexp_names_update ne se in
      let te' = exp_names_update ne te
      in Hpointsto (e',se',te')
  | Hlseg (k,hpara,e1,e2,el) ->
      let hpara' = hpara_names_update ne hpara in
      let e1' = exp_names_update ne e1 in
      let e2' = exp_names_update ne e2 in
      let el' = List.map (exp_names_update ne) el
      in Hlseg (k,hpara',e1',e2',el')
  | Hdllseg (k,hpara_dll,e1,e2,e3,e4,el) ->
      let hpara_dll' = hpara_dll_names_update ne hpara_dll in
      let e1' = exp_names_update ne e1 in
      let e2' = exp_names_update ne e2 in
      let e3' = exp_names_update ne e3 in
      let e4' = exp_names_update ne e4 in
      let el' = List.map (exp_names_update ne) el
      in Hdllseg (k,hpara_dll',e1',e2',e3',e4',el')

and hpara_names_update ne {root=id1;next=id2;svars=idl1;evars=idl2;body=hpredl} =
  let id1' = NameEnv.ident_update ne id1 in
  let id2' = NameEnv.ident_update ne id2 in
  let idl1' = List.map (NameEnv.ident_update ne) idl1 in
  let idl2' = List.map (NameEnv.ident_update ne) idl2 in
  let hpredl' = List.map (hpred_names_update ne) hpredl
  in {root=id1';next=id2';svars=idl1';evars=idl2';body=hpredl'}

and hpara_dll_names_update ne {cell=id1;blink=id2;flink=id3;svars_dll=idl1;evars_dll=idl2;body_dll=hpredl} =
  let id1' = NameEnv.ident_update ne id1 in
  let id2' = NameEnv.ident_update ne id2 in
  let id3' = NameEnv.ident_update ne id3 in
  let idl1' = List.map (NameEnv.ident_update ne) idl1 in
  let idl2' = List.map (NameEnv.ident_update ne) idl2 in
  let hpredl' = List.map (hpred_names_update ne) hpredl
  in {cell=id1';blink=id2';flink=id3';svars_dll=idl1';evars_dll=idl2';body_dll=hpredl'}

let sigma_names_add ns sigma =
  List.iter (hpred_names_add ns) sigma

let sigma_names_update ne sigma =
  List.map (hpred_names_update ne) sigma

let footprint_names_add ns = function
  | None -> ()
  | Some fp ->
      pi_names_add ns fp.foot_pi;
      sigma_names_add ns fp.foot_sigma

let footprint_names_update ne = function
  | None -> None
  | Some fp ->
      Some {foot_pi = pi_names_update ne fp.foot_pi; foot_sigma = sigma_names_update ne fp.foot_sigma}

(** Add the occurring names to the set *)
let prop_names_add ns p =
  sub_names_add ns p.sub;
  pi_names_add ns p.pi;
  sigma_names_add ns p.sigma;
  footprint_names_add ns p.footprint

(** Update the names in the prop *)
let prop_names_update ne p =
  {sub = sub_names_update ne p.sub;
   pi = pi_names_update ne p.pi;
   sigma = sigma_names_update ne p.sigma;
   footprint = footprint_names_update ne p.footprint}

