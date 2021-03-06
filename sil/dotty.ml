(*
 *
 * Copyright (c) 2006-2008,
 *  Cristiano Calcagno    <ccris@doc.ic.ac.uk>
 *  Dino Distefano        <ddino@dcs.qmul.ac.uk>
 *  Peter O'Hearn         <ohearn@dcs.qmul.ac.uk>
 *  Hongseok Yang         <hyang@dcs.qmul.ac.uk>
 * All rights reserved.
 *)


open Ident
open Sil
open Prover

module F = Format

(** {1 Dotty} *)

type kind_of_dotty_prop = Generic_proposition 
			  | Spec_precondition 
			  | Spec_postcondition 
			  | Lambda_pred of int * int

type dotty_node = 
  | Dotpointsto of int * Sil.exp  * Sil.hpred list * int
  | Dotlseg of int * Sil.exp * Sil.exp * Sil.lseg_kind * Sil.hpred list * int 
  | Dotdllseg of int * Sil.exp * Sil.exp *Sil.exp *Sil.exp * Sil.lseg_kind * Sil.hpred list * int



let dangling_boxes = ref []
let exps_neq_zero = ref []

(* general unique counter to assign a different number to boxex, clusters,subgraphs etc.*)
let dotty_state_count = ref 0 

let spec_counter = ref 0
let post_counter = ref 0
let lambda_counter = ref 0
let proposition_counter = ref 0  
let current_pre = ref 0
let spec_id = ref 0
let invisible_arrows = ref false
let invisible_arrows_list = ref []

let sll_attr= ref "style=filled; color=lightgrey; node [style=filled,color=white];"
let dll_attr= ref "style=filled; color=lightgrey; node [style=filled,color=white];" 

let exp_is_neq_zero e =
  List.exists (fun e' -> exp_equal e e') !exps_neq_zero

let pp_exp fmt e =
  let s = if exp_is_neq_zero e then "\\n!=0" else ""
  in F.fprintf fmt "%a%s" pp_exp e s

let exp_to_string e =
  match e with
    Var i -> name_to_string (ident_name i)
  | Const_int i -> string_of_int i
  | Const_fun fn -> name_to_string fn
  | Sizeof _ -> assert false
  | Cast(t,ex) -> assert false
  | UnOp(op,ex) -> assert false
  | BinOp(bin,ex1,ex2) -> assert false
  | Lvar(v) -> assert false
  | Lfield(ex,fn) -> assert false
  | Lindex(ex1,ex2) -> assert false


let rec add_lambda_to_sigma sigma lambda =
    match sigma with 
    [] -> []
  | hp::sigma' -> 
   (hp,lambda):: add_lambda_to_sigma sigma' lambda


let rec look_up_for_back_pointer e dotnodes lambda =
  match dotnodes with
  | [] -> None
  | Dotdllseg(n,_,_,_,e4,_,_,lambda')::dotnodes' -> 
	  if exp_compare e e4 = 0 && lambda=lambda' then Some (n+1)  
	  else look_up_for_back_pointer e dotnodes' lambda
  | _::dotnodes' ->look_up_for_back_pointer e dotnodes' lambda


let rec look_up dotnodes lpair e lambda = 
  match lpair with
    [] -> look_up_for_back_pointer e dotnodes lambda
  |(n,e',lambda')::lpair' -> 
       if exp_compare e e' = 0 && lambda=lambda' then Some n
       else look_up dotnodes lpair' e lambda


let pp_nesting fmt nesting =
  if nesting>1 then F.fprintf fmt "%d" nesting

let reset_proposition_counter () = proposition_counter:=0

let reset_dotty_spec_counter () = spec_counter:=0

let max_map f l =
  let curr_max = ref 0 in
    List.iter (fun x -> curr_max := max !curr_max (f x)) l;
    ! curr_max

let rec sigma_nesting_level sigma =
  max_map (function
    | Hpointsto _ -> 0
    | Hlseg (_,hpara,_,_,_) -> hpara_nesting_level hpara
    | Hdllseg (_,hpara_dll,_,_,_,_,_) -> hpara_dll_nesting_level hpara_dll) sigma

and hpara_nesting_level hpara =
  1 + sigma_nesting_level hpara.body

and hpara_dll_nesting_level hpara_dll =
  1 + sigma_nesting_level hpara_dll.body_dll


let rec dotty_mk_node sigma =
  let n = !dotty_state_count in
  let _ = incr dotty_state_count in
  match sigma with 
    [] -> []
  | (Hpointsto (e,se,t),lambda)::sigma' -> 
      Dotpointsto(n,e,Prop.prop_get_sigma Prop.prop_emp,lambda)::dotty_mk_node sigma'
  | (Hlseg (k,hpara,e1,e2,elist),lambda)::sigma' -> 
      let _ = incr dotty_state_count in  (* increment once more n+1 is the box for last element of the list *)    
      Dotlseg(n,e1,e2,k,hpara.body,lambda)::dotty_mk_node sigma'
  | (Hdllseg (k,hpara_dll,e1,e2,e3,e4,elist),lambda)::sigma'-> 
      let _ = incr dotty_state_count in  (* increment once more n+1 is the box for e4 *)    
      Dotdllseg(n,e1,e2,e3,e4,k,hpara_dll.body_dll,lambda)::dotty_mk_node sigma' 

let set_exps_neq_zero pi =
  let f = function
    | Aneq (e, Const_int 0) -> exps_neq_zero := e :: !exps_neq_zero
    | _ -> ()
  in
    exps_neq_zero := [];
    List.iter f pi




let box_dangling e =
  let entry_e=List.filter (fun (e',n)-> exp_equal e e') !dangling_boxes in
  match  entry_e with 
  |[] -> None 
  |(e',n)::_ -> Some n 
     

let rec look_up_and_add_field lbox_with_label lpair (fname:string) se p f in_struct lambda = 
  match se with
    Eexp e ->
      if (exp_compare e (Const_int 0) =0) or (Prover.check_equal p e (Const_int 0))  then 
	let n' = !dotty_state_count in
 	let _ = incr dotty_state_count in
	let _=F.fprintf f "state%iL%i [label=\"NIL \", color=green, style=filled]\n" n' lambda in
	let _= if !invisible_arrows then 
	  invisible_arrows_list:= ((n',lambda),(!spec_id,0)):: !invisible_arrows_list
	else ()
	in [(n',fname)] 
      else 
	let e' = look_up lbox_with_label lpair e lambda in
	(match e' with 
	 |None -> 
	 (match box_dangling e with  
	  | None -> 
	      if !Config.condensed_dotty && in_struct then []
	      else (
		let n' = !dotty_state_count in
 		let _ = incr dotty_state_count in
		let _=F.fprintf f "state%iL%i [label=\"%a \", color=red, style=filled]\n" n' lambda  pp_exp e in dangling_boxes:=(e,n')::!dangling_boxes;
		let _= if !invisible_arrows then 
		  invisible_arrows_list:= ((n',lambda),(!spec_id,0)):: !invisible_arrows_list
		else ()
		in [(n',fname)]
	      )
	  | Some n' -> [(n',fname)]
	 )

	 |Some n -> [(n,fname)]  
	)
  | Estruct sel' ->
      (match sel' with
	 [] -> []
       | (fn,se2)::l' -> 
	   let fpath = fname ^ "." ^ (name_to_string fn)
	   in look_up_and_add_field  lbox_with_label lpair fpath se2 p  f  true lambda @
		look_up_and_add_field  lbox_with_label lpair fname (Estruct  l') p f true lambda
      )

  | Earray (idx,esel) -> 
      (match esel with
	 [] -> []
       | (e3,se3)::l' -> 
	   let fpath = fname ^ "[" ^ (exp_to_string e3) ^ "]"
	     in
	     look_up_and_add_field  lbox_with_label lpair fpath se3  p f  in_struct lambda @
	       look_up_and_add_field  lbox_with_label lpair fname (Earray (idx, l')) p f in_struct lambda
      )

let rec dotty_mk_links dotnodes lbox sigma p f =
  match sigma with
    [] -> []
    | (Hpointsto (e,se,t),lambda)::sigma' -> 
	let src=look_up dotnodes lbox e lambda in
	(match src with 
	  None -> 
	    assert false
	| Some n ->
	   let target_list =  
 	     look_up_and_add_field  dotnodes lbox "" se p f false lambda
	   in (List.map (fun (m,lab) -> (n,m,lab,lambda)) target_list) 
	      @ dotty_mk_links  dotnodes lbox sigma' p f
	)

  | (Hlseg (_,pred,e1,e2,elist),lambda)::sigma' -> 
  	let src=look_up dotnodes lbox e1 lambda in
	(match src with  
	  None ->assert false
 	| Some n ->
 	    let (m,lab)=List.hd (look_up_and_add_field  dotnodes lbox "Next" (Eexp e2) p f false lambda) in
	    (n+1,m ,lab,lambda)::dotty_mk_links  dotnodes lbox sigma' p f
	)
  | (Hdllseg (_,pred,e1,e2,e3,e4,elist),lambda)::sigma' -> 
   	let src=look_up dotnodes lbox e1 lambda in
  	(match src with  
 	  None ->assert false
  	| Some n -> (* n is e1's box  and n+1 is e4's box *)
  	    let targetF = look_up dotnodes lbox e3 lambda in
  	    let target_Flink= (match targetF with
 				 None -> []
			       | Some m -> [(n+1,m,"Flink",lambda)]
			      ) in
  	    let targetB = look_up dotnodes lbox e2 lambda in
	    let target_Blink= (match targetB with
 				 None -> []
			       | Some m -> [(n,m,"Blink",lambda)]
			      ) in
 	    target_Blink @ target_Flink @ dotty_mk_links dotnodes lbox sigma' p f
	)  


let make_simplified_node dotnode =
  match dotnode with 
  | Dotpointsto (a,b,_,lambda) -> (a,b,lambda)
  | Dotlseg  (a,b,_,_,_,lambda) -> (a,b,lambda)
  | Dotdllseg  (a,b,_,_,_,_,_,lambda) -> (a,b,lambda)
  
    

let  print_kind f kind =
  incr dotty_state_count;
  let _=match kind with 
    | Spec_precondition ->
	current_pre:=!dotty_state_count;
	incr dotty_state_count;
	F.fprintf f "\n state%iL0 [label=\"PRE %i \",  style=filled, color= yellow]\n" !dotty_state_count  !spec_counter 
    | Spec_postcondition ->
	F.fprintf f "\n state%iL0 [label=\"POST %i \",  style=filled, color= yellow]\n" !dotty_state_count !post_counter; 
	invisible_arrows_list:=((!spec_id,0), (!dotty_state_count,0)):: !invisible_arrows_list
    | Generic_proposition ->
	F.fprintf f "\n state%iL0 [label=\"PROP %i \",  style=filled, color= yellow]\n" !dotty_state_count !proposition_counter 
    | Lambda_pred (no,lev) ->
	F.fprintf f "style=dashed; color=blue \n state%iL%i [label=\"INTERNAL STRUCTURE %i \",  style=filled, color= lightblue]\n" !dotty_state_count !lambda_counter !lambda_counter ;
	F.fprintf f "state%iL%i -> state%iL%i [color=\"lightblue \"] \n"  !dotty_state_count !lambda_counter no lev
  in incr dotty_state_count


let  dotty_pp_link f (n1,n2,lab,lambda)  =
    if n2=0 then 
      F.fprintf f "state%iL%i -> state%iL%i[label=\"%s DANG\", color= red];\n" n1 lambda n2 lambda lab
    else 
      F.fprintf f "state%iL%i -> state%iL%i[label=\"%s\"];\n" n1 lambda n2 lambda lab
   




let rec print_sll nesting k f n e1 e2 lambda=
  let n' = !dotty_state_count in
  let _ = incr dotty_state_count in

  begin
   match k with
    | Lseg_NE -> F.fprintf f "subgraph cluster_%iL%i { %s label=\"lsNE\";" n' lambda !sll_attr 
    | Lseg_PE -> F.fprintf f "subgraph cluster_%iL%i { %s label=\"lsPE\";" n' lambda !sll_attr 
  end;
  F.fprintf f "state%iL%i [label=\"%a\"]\n" n lambda  pp_exp e1;
  let n' = !dotty_state_count in
  let _ = incr dotty_state_count in
  F.fprintf f "state%iL%i [label=\"... \" style=filled color=lightgrey] \n" n' lambda ;
  F.fprintf f "state%iL%i -> state%iL%i [label=\"Next \"] \n" n lambda  n' lambda ;
  F.fprintf f "state%iL%i [label=\" \"] \n" (n+1) lambda  ;
  F.fprintf f "state%iL%i -> state%iL%i [label=\"Next \"] }" n' lambda (n+1) lambda ;
  incr lambda_counter;
  pp_dotty f (Lambda_pred(n+1,lambda)) (Prop.prop_of_sigma nesting)  

and print_dll nesting k f n e1 e2 e3 e4 lambda =
  let n' = !dotty_state_count in
  let _ = incr dotty_state_count in
  let _ =
    match k with
    | Lseg_NE -> F.fprintf f "subgraph cluster_%iL%i { %s label=\"dlsNE%a\";" n' lambda !dll_attr  
    | Lseg_PE -> F.fprintf f "subgraph cluster_%iL%i { %s label=\"dlsPE%a\";" n' lambda !dll_attr  
  in
  F.fprintf f "state%iL%i [label=\"%a\"]\n" n lambda pp_exp e1;
  let n' = !dotty_state_count in
  let _ = incr dotty_state_count in
  F.fprintf f "state%iL%i [label=\"... \" style=filled color=lightgrey] \n" n' lambda ;
  F.fprintf f "state%iL%i -> state%iL%i [label=\"Flink\"]\n" n lambda n' lambda;  
  F.fprintf f "state%iL%i -> state%iL%i [label=\"Blink\"]\n" n' lambda n lambda;  
  F.fprintf f "state%iL%i [label=\"%a\"]\n" (n+1) lambda pp_exp e4;
  F.fprintf f "state%iL%i -> state%iL%i [label=\"Blink\"]\n" (n+1) lambda n' lambda;  
  F.fprintf f "state%iL%i -> state%iL%i [label=\"Flink\"]}\n" n' lambda  (n+1) lambda ;
  incr lambda_counter;
  pp_dotty f (Lambda_pred(n',lambda)) (Prop.prop_of_sigma nesting) 
  

and  dotty_pp_state f dotnode  =
  match dotnode with 
  | Dotpointsto(n,e1,nesting,lambda) -> 
      F.fprintf f "state%iL%i [label=\"%a\"]\n" n lambda  pp_exp e1
  | Dotlseg(n,e1,e2, Lseg_NE,nesting,lambda) -> 
      print_sll nesting Lseg_NE f n e1 e2 lambda 
  | Dotlseg(n,e1,e2, Lseg_PE,nesting,lambda) -> 
      print_sll nesting Lseg_PE f n e1 e2 lambda
  | Dotdllseg(n,e1,e2,e3,e4,Lseg_NE,nesting,lambda) -> 
      print_dll nesting Lseg_NE f n e1 e2 e3 e4 lambda 
  | Dotdllseg(n,e1,e2,e3,e4,Lseg_PE,nesting,lambda)-> 
      print_dll nesting Lseg_PE f n e1 e2 e3 e4 lambda


(* Build the graph data structure to be printed *)
and build_visual_graph f p =
  let sigma =Prop.prop_get_sigma p  in 
  let sigma_lambda = add_lambda_to_sigma sigma !lambda_counter in
  let nodes=dotty_mk_node sigma_lambda in
  let simplified_nodes=List.map make_simplified_node nodes in
  let links=dotty_mk_links nodes simplified_nodes sigma_lambda p f in
  (nodes,links)



(** Pretty print a proposition in dotty format. *)
and pp_dotty f kind p =
  incr proposition_counter;
  dangling_boxes := [];
  set_exps_neq_zero (Prop.prop_get_pi p);
  incr dotty_state_count;
  let _=F.fprintf f "\n subgraph cluster_%i { color=black \n" !dotty_state_count in 
  print_kind f kind;
  let (nodes,links)=build_visual_graph f p in
  List.iter  (dotty_pp_state f) nodes;
  List.iter (dotty_pp_link f) links;
  let _=F.fprintf f "\n } \n" in ()



let pp_dotty_one_spec f pre posts =
  invisible_arrows_list:=[];
  post_counter :=0;
  incr spec_counter;
  incr proposition_counter;
  incr dotty_state_count;
  let _=F.fprintf f "\n subgraph cluster_%i { color=blue \n" !dotty_state_count in 
  incr dotty_state_count;
  let _=F.fprintf f "\n state%iL0 [label=\"SPEC %i \",  style=filled, color= lightblue]\n" !dotty_state_count !spec_counter in 
  spec_id:=!dotty_state_count;
  invisible_arrows:=true;
  pp_dotty f (Spec_precondition) pre; 
  invisible_arrows:=false;
  List.iter (fun po -> incr post_counter ; pp_dotty f (Spec_postcondition) po)  posts; 
  List.iter (fun ((n1,lam1),(n2,lam2)) -> 
	       F.fprintf f "state%iL%i ->state%iL%i [style=invis]\n" n1 lam1 n2 lam2) !invisible_arrows_list;
  let _=F.fprintf f "\n } \n" in ()


let pp_dotty_prop_list f plist prev_n curr_n=
  incr proposition_counter;
  incr dotty_state_count;
  let _=F.fprintf f "\n subgraph cluster_%i { color=blue \n" !dotty_state_count in 
  incr dotty_state_count;
  let _=F.fprintf f "\n state%iN [label=\"NODE %i \",  style=filled, color= lightblue]\n"  curr_n curr_n in 
  List.iter (fun po -> incr proposition_counter ; pp_dotty f (Generic_proposition) po)  plist; 
  if prev_n <> -1 then F.fprintf f "\n state%iN ->state%iN\n"  prev_n curr_n;  
  let _=F.fprintf f "\n } \n" in ()

