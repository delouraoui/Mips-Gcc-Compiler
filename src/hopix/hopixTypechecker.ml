(** This module implements a type checker for Datix. *)
open HopixAST
open Position
open HopixTypes
open HopixPrettyPrinter

let initial_typing_environment = HopixTypes.initial_typing_environment
type typing_environment = HopixTypes.typing_environment

let type_error = Error.error "typechecking"

let located f x = f (Position.position x) (Position.value x)

let equals_contr a b = 
  match a , b with 
  | TCon a', TCon b' -> a' = b' 
let equals_Kid a b = 
  match a , b with 
  | KId a', KId b' -> a' = b'

let rec equal_Ty x y = 
  match x , y with
  | TyCon( TCon(a),[]),TId x ->
     a = x
  | TyCon( TCon(a),b::q),TId x -> 
     if a = x then true 
     else equal_Ty (Position.value b) y
  | TyVar( TId a ),TId x -> a = x 

let rec substall lsub = function
  | TyVar x'  as var ->
     begin
       try
	 let l' = Dict.to_list lsub in
	 
	 (snd (List.find (fun (a,b) -> x' = a) l'))
       with Not_found ->
	 var
     end
  | TyCon (a, l) ->
     (fun y ->
      let y', pos = Position.destruct y in
      let y'' = substall lsub y' in
      Position.with_pos pos y'')
     |> (fun x -> List.map x l)
     |> fun x -> TyCon (a, x)


let ( <-- ) x l =
  substall l x

let equals_Lid a b = 
  match a , b with 
  | LId a', LId b' -> a' = b' 

let string_constr = (fun (TCon a) -> a )
let string_Konstr = (fun (KId a) -> a )
let string_var = (fun (TId a) -> a )
let string_label = (fun (LId a) -> a )

let arrow i o = TyCon (TCon "->", [i; o])

let ( --> ) i o = arrow (Position.unknown_pos i) (Position.unknown_pos o)


module SimpleTypes = struct

    (** A program is fully annotated if the programmer wrote a type
      annotation on variables of patterns and has given the return
      type of recursive functions. The following function checks if an
      input program is fully annotated. If not, a type error is
      issued. *)

    let  types_of_label' lab tenv =
      match (types_of_label tenv lab) with 
      | None -> failwith "impossible"
      | Some (t,p,lty) -> (t,p,lty)
    let  type_of_label' lab tenv =
      match (types_of_label tenv lab) with 
      | None -> failwith "impossible"
      | Some (t,p,lty) -> (t,lty)
    let type_of_constr constr tenv = 
      match (types_of_constructor tenv constr) with 
      | None -> failwith "impossible"
      | Some (t,p,lty) -> (t,lty)
    let rec check_program_is_fully_annotated p = 
      let f = fun x ->
	x |> Position.value |> check_definition_is_fully_annotated
      in
      List.iter f p

    and check_definition_is_fully_annotated w = match w with
      | DeclareExtern _ -> () 
      | DefineValue (x, e) ->
	 (match Position.value e with
	  | TypeAnnotation (e', ty) ->
	     check_expression_is_fully_annotated (Position.value e')
	  | _ -> failwith "o Bad annotation1")
      | DefineRecValue l ->
	 check_recdefine_is_fully_annotated l
      | DefineType _ -> ()

    and check_expression_is_fully_annotated expr = match expr with
	
      | Literal _ | Variable _ -> ()
				    
      | Define (x, e1, e2) ->
	 (match Position.value e1, Position.value e2 with
	  | TypeAnnotation (e1', _), TypeAnnotation (e2', _) ->
	     check_expression_is_fully_annotated (Position. value e1');
	     check_expression_is_fully_annotated (Position. value e2')
	  | _ -> failwith "u Bad annotation2")
	   
      | DefineRec (l, e) ->
	 check_recdefine_is_fully_annotated l;
	 (match Position.value e with
	  | TypeAnnotation (e', _) ->
	     check_expression_is_fully_annotated (Position.value e')
	  | _ -> failwith "Bad annotation3")
           
      | Apply (a, b) ->
	 (match Position.value a, Position.value b with
	  | TypeAnnotation (a', _), TypeAnnotation (b', _) ->
	     check_expression_is_fully_annotated (Position. value a');
	     check_expression_is_fully_annotated (Position. value b')
	  | _ -> failwith "Bad annotation4")
	   
      | IfThenElse (b, e1, e2) ->
	 (match Position.value b, Position.value e1, Position.value e2 with
	  | TypeAnnotation(b',_),TypeAnnotation(e1',_),TypeAnnotation(e2',_) ->
	     check_expression_is_fully_annotated(Position.value b');
	     check_expression_is_fully_annotated(Position.value e1');
	     check_expression_is_fully_annotated(Position.value e2')
	  | _ -> failwith "Bad annotation5")
	   
      | Fun (p, e) ->
	 (match Position.value p, Position.value e with
	  | PTypeAnnotation (p',_), TypeAnnotation (e',_) ->
	     check_pattern_is_fully_annotated (Position.value p');
	     check_expression_is_fully_annotated(Position.value e')
	  | _ -> failwith "Bad annotation6")
	   
      | Tagged (_,le) ->
	 let f = fun x ->
	   x |> Position.value |> check_expression_is_fully_annotated
	 in
	 List.iter f le
		   
      | Case (e, lb) ->
	 (match Position.value e with
	  | TypeAnnotation (e',_) ->
	     check_expression_is_fully_annotated (Position.value e')
	  | _ -> failwith "Bad annotation7");
	 let f = fun x ->
	   x |> Position.value |> check_branch_is_fully_annotated
	 in
	 List.iter f lb

      | Record r ->
	 let f = fun (x,y) ->
	   y |> Position.value |> check_expression_is_fully_annotated
	 in
	 List.iter f r
      | TypeAnnotation(x,y) -> 
         check_expression_is_fully_annotated(Position.value x)

      | Field(e, lab) -> 
	 (match Position.value e with
	  | TypeAnnotation (e', _) ->
	     check_expression_is_fully_annotated (Position.value e')
	  | _ -> failwith "Bad annotation9")

      | ChangeField(e1, l, e2) -> 
	 (match Position.value e1, Position.value e2 with
	  | TypeAnnotation(e1',_),TypeAnnotation(e2',_) ->
	     check_expression_is_fully_annotated(Position.value e1');
	     check_expression_is_fully_annotated(Position.value e2')
	  | _ -> failwith "Bad annotation10")

    and check_recdefine_is_fully_annotated p = 
      match p with 
      | [] -> ()
      | (f, e)::tl ->
	 (match Position.value e with
	  | TypeAnnotation (e', _) ->
	     check_expression_is_fully_annotated (Position.value e')
	  | _ -> failwith "h Bad annotation");
	 check_recdefine_is_fully_annotated tl

    and check_branch_is_fully_annotated = fun (Branch (p, e)) ->
      (match Position.value p, Position.value e with
       | PTypeAnnotation (p',_),TypeAnnotation (e',_) ->
	  check_pattern_is_fully_annotated  (Position.value p');
	  check_expression_is_fully_annotated (Position.value  e')
       | _ -> failwith "Bad annotation")

    and check_pattern_is_fully_annotated expr = match expr with
	
      | (PVariable _ | PLiteral _ | PWildcard) -> ()

      | PRecord r ->
	 let f = fun (x,y) ->
	   y |> Position.value |> check_pattern_is_fully_annotated
	 in
	 List.iter f r
      | (POr l | PAnd l) ->
	 let f = fun x ->
	   x |> Position.value |> check_pattern_is_fully_annotated
	 in
	 List.iter f l

      | PTaggedValue (_, lp) ->
	 let f = fun x ->
	   x |> Position.value |> check_pattern_is_fully_annotated
	 in
	 List.iter f lp
		   
      | PTypeAnnotation (e,ty) ->
	 check_pattern_is_fully_annotated (Position.value  e)
	 
				    
    let undress_expression exp = match exp with
      | TypeAnnotation (e, ty) -> (e, ty)
      | _ -> assert false (* by is_fully_annotated. *)

    let undress_pattern exp = match exp with
	
      | PTypeAnnotation (p, ty) -> (p, ty)
      | _ -> assert false (* by is_fully_annotated. *)

    let rec check_types0 pos xty ity = 
	if xty <> ity then
	  type_error pos
		     (Printf.sprintf "Expecting: %s\n  Inferred: %s"
				     (to_string ty xty)
				     (to_string ty ity))

    let rec  check_types pos xty ity = match xty, ity with
	| TyCon (TCon "->", [a;b]), TyCon (TCon "->", [a';b']) ->
	   check_types pos (Position.value a) (Position.value a');
	   check_types pos (Position.value b) (Position.value b')
	| _ ->
	   check_types0 pos xty ity

      and arrow_type arty = 
	match arty with
	| TyCon (TCon "->",[a;b]) -> a, b
	| _ -> assert false

		    

    (**

     [typecheck tenv p] returns the typing environment
     augmented with the variables defined by the program.

     We first check that [p] is fully annotated. Then,
     the algorithm is meant to check that annotation are
     consistent.

     For programs and definitions, the algorithm is a straightforward
     traversal of the abstract syntax tree. Each node of the abstract
     syntax tree is locally checked for welltypedness: indeed, there
     is exactly one typing rule per syntactic construction and this
     rule only requires the subexpressions have been recursively
     checked.

     For expressions, things are a bit more complicated since some
     nodes of the abstract syntax tree do not carry a type annotation.
     For these nodes, we do not *check* that the expression has some
     type but we *compute* a type instead. Therefore, we must
     implement two mutually recursive functions: one that checks if an
     input expression has a specific type (in that case, the
     expression and the type are inputs) and another one which compute
     a type for a given expression (in that casse, the expression is
     the input and the type is the output).

     *)

    

    (************************************************ Begin Well Formed Expression *************************************)
   let rec bind_SumType  (tcon,ts,tdef) tenv = function
      | [] -> tenv
      | (constr,typelist) :: q  ->
           (**  verifier que le constructeur n'existe pas dÃ©ja *)
	 let tenv' = bind_types_of_constructor tenv constr (tcon,ts,typelist) in
           bind_SumType  (tcon,ts,tdef) tenv' q

    let rec bind_RecType  (tcon,ts,tdef) tenv  = function
      | [] -> tenv
      | (lab, ty)::q  ->
         (**  verifier que le constructeur n'existe pas dÃ©ja *)
	 let tenv' = bind_types_of_label tenv lab (tcon,ts,tdef) in
         bind_RecType (tcon,ts,tdef) tenv' q
    let rec  bind_all_types (tcon,ts) tenv = function
      | DefineSumType l ->  bind_SumType  (tcon,ts,[]) tenv
					  (List.map (fun (k,l') -> ((Position.value k),(List.map Position.value l'))    )  l)
      | DefineRecordType l ->
	 let vvv = (List.map (fun (a,b) -> ((Position.value a),( Position.value b)))  l) in 
	 bind_RecType  (tcon,ts,vvv) tenv vvv
      | Abstract -> tenv
		      
     let rec  check_constr_not_in_env constr tenv pos = 
	match (types_of_constructor tenv constr) with 
        | None -> ()
        | Some (x,_,_) -> 
           type_error pos (Printf.sprintf "The constructor `%s' has already declared."
					  (string_Konstr constr) )
		      
      let rec check_konstr_in_env constr length tenv pos = 
	match (types_of_constructor tenv constr) with 
        | None ->
	   type_error pos
		      (Printf.sprintf "Unknown constructor `%s'."
				      (string_Konstr constr) )
        | Some (t,p,lty) when length = (List.length lty) -> lty
        | Some (t,p,lty) ->
	   type_error pos
		      (Printf.sprintf "The constructor `%s' has %d arguments "
				      (string_Konstr constr) (List.length lty) )

     let rec check_label_not_in_env label tenv pos = 
	match (types_of_label tenv label) with 
        | None -> ()
        | Some (_,_,_) -> 
           type_error pos (Printf.sprintf "The constructor `%s' has already declared." (string_label label) )

      let rec check_label_in_env label length tenv pos = 
	match (types_of_label tenv label) with 
        | None ->
	   type_error pos (Printf.sprintf "Unknown label `%s' ."
						 (string_label label) )
        | Some (_,_,l) when length = (List.length l)  -> l
        | Some (_,_,l)  ->
	   type_error pos (Printf.sprintf "The record `%s' has %d arguments "
					  (string_label label) (List.length l) )

      let rec check_label_in_envS label tenv pos = 
	match (types_of_label tenv label) with 
        | None ->
	   type_error pos (Printf.sprintf "Unknown label `%s' ."
					  (string_label label) )
        | Some (_,_,_)  -> ()

      and type_of_label_in_env label tenv pos = 
	match (types_of_label tenv label) with 
        | None ->
	   type_error pos (Printf.sprintf "Unknown label `%s' ."
					  (string_label label) )
        | Some (_,_,l)  -> (List.assoc label l )  

      let rec check_constr_in_env constr tenv pos  = 
	match (lookup_type_definition constr tenv) with 
        | None -> type_error pos (Printf.sprintf "The constructor `%s' has not declared." (string_constr constr) )
        | Some (_,_) -> ()
			  
      let rec check_type_list konstr pos tenv = function 
	| [] -> ()
	| a::q -> 
           match (Position.value a) with
           | (TyCon(constr,typ)) ->
              check_constr_in_env (constr) tenv pos;
              check_type_list konstr pos tenv q
           | _ -> check_type_list konstr pos tenv q

      let rec check_not_two_same lab k pos = function 
	| [] when (k < 2) -> ()
	| [] ->
	   type_error pos
		      (Printf.sprintf "The variable `%s' has two occurence."
				      (string_label lab) )
	| (a, ty)::q when equals_Lid lab (Position.value a)-> 
           check_not_two_same lab (k+1) pos q
	| a::q -> check_not_two_same lab k pos q

      let rec well_formed_SumType  tenv ts pos = function
	| [] -> ()
	| (constr,typelist) :: q  ->
           (**  verifier que le constructeur n'existe pas dÃ©ja *)
           check_constr_not_in_env (Position.value constr) tenv pos;
           check_type_list (Position.value constr) pos tenv typelist;
           well_formed_SumType tenv ts pos q

      let rec well_formed_RecType  tenv ts pos varslist = function
	| [] -> ()
	| (lab, ty)::q  ->
           (**  verifier que le constructeur n'existe pas dÃ©ja *)
           check_label_not_in_env (Position.value lab) tenv pos;
           check_not_two_same (Position.value lab) 0 pos varslist;
           well_formed_RecType tenv ts pos varslist q

      let rec well_formed_type_definition tenv ts pos = function
	| DefineSumType (l) -> 
           well_formed_SumType tenv ts pos l
	| DefineRecordType (l) -> 
           well_formed_RecType tenv ts pos l l
	| Abstract -> ()

      (************************************************ End Well Formed Expression *************************************)
let rec check_pattern tenv xty pos = function
	| PWildcard -> tenv 

	| PLiteral l -> tenv

	| PVariable v ->
	   (**Printf.printf " ptype : %s \n " (to_string pattern (PVariable v));**)
	   bind_value_type (Position.value v) xty tenv

	| PTypeAnnotation (e, ty) -> 
	   check_pattern tenv (Position.value ty) pos (Position.value e)   

	| PTaggedValue(k,l) -> 
	   let list_types = 
	     check_konstr_in_env (Position.value k) (List.length l) tenv pos in 
	   check_Ptype_sum' tenv pos l  list_types

	| POr l -> 
	   List.fold_left 
	     (fun a patt -> 
	      check_pattern a xty pos (Position.value patt) 
	     ) tenv l

	| PAnd l -> 
	   List.fold_left 
	     (fun a patt -> 
	      check_pattern a xty pos (Position.value patt) 
	     ) tenv l

	| PRecord (l) -> 
	   begin
	     match l with
	     | [] -> type_error pos (Printf.sprintf "Empty record.")
	     | (label,exp)::q -> 
		let list_types =
		  check_label_in_env (Position.value label) (List.length l) tenv pos in
		check_Ptype_rec' tenv pos l list_types
	   end
and check_Ptype_rec' tenv pos l l' = 
	match l,l' with
	| [] ,[]  -> tenv
	| (lab,a)::q, (label,ty)::q' ->
	   begin
	     match Position.value lab , Position.value a with
	     | label', PTypeAnnotation (e', ty') 
		  when (equals_Lid label label') ->
		let _ = check_types pos ty (Position.value ty') in 
		let tenv' = 
		  check_pattern tenv (Position.value ty') pos (Position.value e') in
		check_Ptype_rec' tenv' pos q q'
	     | _, _ ->  failwith "Error"
	   end
	| _,_ -> failwith "impossible"

and check_Ptype_sum' tenv pos l l'= 
	match l,l' with
	| [] ,[]  -> tenv
	| a::q, ty::q' ->
	   begin
	     match Position.value a with
	     | PTypeAnnotation (e', ty') ->
		check_types pos ty (Position.value ty'); 
		let tenv' = 
		  check_pattern tenv (Position.value ty') pos (Position.value e') in
		check_Ptype_sum' tenv' pos q q'
	     | _ -> failwith "s bad annotation"
	   end
	| _,_ -> failwith "impossible"
	        
let rec check_pattern' tenv xty pos = function
	| PWildcard -> tenv 

	| PLiteral l -> tenv

	| PVariable v ->
	   (*Printf.printf "Pvariable %s %s \n" (to_string pattern ((PVariable  v) )) (to_string ty xty); *)
	   bind_value_type (Position.value v) xty tenv

	| PTypeAnnotation (e, ty) ->
	   begin
	   match Position.value e with
	   | PVariable v -> check_pattern' tenv (xty) pos (Position.value e) 
	   |  _ -> 
	       check_pattern' tenv (Position.value ty) pos (Position.value e)   
	   end
	| PTaggedValue(k,l) ->
	   let ltyp = type_of_constr (Position.value k) tenv in
	   List.fold_left2 (fun env ty' e ->
			    (**Printf.printf "Ptagged %s type %s \n" (to_string pattern (Position.value e)) (to_string ty ty'); **)
		      check_pattern' env ( ty') pos (Position.value e)
		     ) tenv (snd ltyp) l
				 
	| POr l -> 
	   List.fold_left 
	     (fun a patt -> 
	      check_pattern' a xty pos (Position.value patt) 
	     ) tenv l

	| PAnd l -> 
	   List.fold_left 
	     (fun a patt -> 
	      check_pattern' a xty pos (Position.value patt) 
	     ) tenv l

	| PRecord (l) ->
	   
	   let ltyp = type_of_label' (Position.value (fst (List.hd l)) ) tenv in
	   let vvv = (List.map (fun (a,b) ->
				let lty1 = List.assoc (Position.value a) (snd ltyp) in
				((Position.value a),lty1))  l) in
	   let env2 = (List.fold_left (fun env1 (a,b) ->
				       let lty1 = List.assoc (Position.value a) (snd ltyp) in
				check_pattern' env1 lty1 pos (Position.value b) ) tenv l) in 
	   let (tcon,ts,tdef) = types_of_label' (Position.value (fst (List.hd l)) ) env2 in
           bind_RecType (tcon,ts,vvv) env2 vvv

			  
      let typecheck tenv p =
      check_program_is_fully_annotated p;

      let rec program tenv p =
	List.fold_left (fun tenv -> located (definition tenv)) tenv p
      and definition tenv pos = function
	| DeclareExtern (x, ty) ->
           bind_value_type (Position.value x) (Position.value ty) tenv

	| DefineValue (x, e) ->
	   check_definition tenv pos (x, e)
			    
	| DefineType (tcon, ts, tdef) ->
	   let new_tenv = bind_type_definition
			    (Position.value tcon)
			    (List.map Position.value ts)
			    tdef
			    tenv in
	   let env' =  bind_all_types ((Position.value tcon),(List.map Position.value ts)) new_tenv tdef in
	   (**well_formed_type_definition env' ts pos tdef;**)
	   env'
	     

	| DefineRecValue rdefs ->
	   (* check_rec_definitions t *)
	   let new_tenv =
	     List.fold_left get_tenv_definerec tenv rdefs
	   in
	   List.iter (check_one_definerec new_tenv) rdefs;
	   new_tenv

      and bind_definition tenv (x, e) =
	HopixTypes.bind_value_type x e tenv

      and check_type_sum tenv pos l l'= 
	match l,l' with
	| [] ,[]  -> ()
	| a::q, ty::q' ->
	   begin
	     match Position.value a with
	     | TypeAnnotation (e', ty') ->
		check_types pos ty (Position.value ty'); 
		check_expression tenv (Position.value ty') pos (Position.value e');
		check_type_sum tenv pos q q'
	     | _ -> failwith "y bad annotation"
	   end
	| _,_ -> failwith "impossible"

      and check_type_rec tenv pos l l' = 
	match l,l' with
	| [] ,[]  -> ()
	| (lab,a)::q, (label,ty)::q' ->
	   begin
	     match Position.value lab , Position.value a with
	     | label', TypeAnnotation (e', ty') when (equals_Lid label label') ->
  		check_types pos ty (Position.value ty'); 
  		check_expression tenv (Position.value ty') pos (Position.value e');
  		check_type_rec tenv pos q q'
	     | _, _ ->  failwith "Error"
	   end
	| _,_ -> failwith "impossible"


      and check_definition tenv pos (x, e) =  
	match Position.value e with
	| TypeAnnotation (e', ty) ->
           check_expression tenv (Position.value ty) pos (Position.value e');
           bind_value_type (Position.value x) (Position.value ty) tenv
	| _ -> assert false

      and check_expression tenv xty pos = function
	| Literal x ->
	   check_types pos xty (located (literal tenv) x)
	| Variable x ->
	   let x, pos = Position.destruct x in
	   begin match lookup_value_type x tenv with
		 | Some ity ->
		    check_types pos xty ity
		 | None ->
		    let Id s = x in
		    type_error pos (Printf.sprintf "Unbound identifier `%s'." s)
	   end
	| Define (x, e1, e2) ->
	   let e1', pos1 = Position.destruct e1 in
	   let e1'', ty1 = undress_expression e1' in
	   check_expression tenv (Position.value ty1) pos1 (Position.value e1'');
	   let new_tenv =
	     bind_definition tenv (Position.value x, Position.value ty1)
	   in
	   let e2', pos2 = Position.destruct e2 in
	   let e2'', ty2 = undress_expression e2' in
	   check_expression new_tenv (Position.value ty2) pos2 (Position.value e2'')

	| DefineRec (l, e) ->
	   let new_tenv =
	     List.fold_left get_tenv_definerec tenv l
	   in
	   List.iter (check_one_definerec new_tenv) l;
	   let e', pose = Position.destruct e in
	   let e'', tye = undress_expression e' in
	   check_expression new_tenv (Position.value tye) pose (Position.value e'');
	   check_types pos xty (Position.value tye)
		       
	| Tagged(k,l) -> 
           let list_types = check_konstr_in_env (Position.value k) (List.length l) tenv pos in 
           check_type_sum tenv pos l list_types

	| Fun (patt, expr) ->

	   let patt', pospatt = Position.destruct patt in
	   let patt'', typatt = undress_pattern patt' in
	   let new_tenv = 
	     check_pattern tenv (Position.value typatt) pospatt (Position.value patt'')
	   in

	   let expr', posexpr = Position.destruct expr in
	   let expr'', tyexpr = undress_expression expr' in

	   (** c'est le type x -> e normalement *)
	   check_expression new_tenv (Position.value tyexpr) posexpr (Position.value expr'');
           
	   let ty1, ty2 = arrow_type xty in
	   check_types pos (Position.value ty1) (Position.value typatt);
	   check_types pos (Position.value ty2) (Position.value tyexpr)
		       
	| Apply (a, b) ->
	   let a', posa = Position.destruct a in
	   let a'', tya = undress_expression a' in
	   check_expression tenv (Position.value tya) posa (Position.value a'');

	   let b', posb = Position.destruct b in
	   let b'', tyb = undress_expression b' in
	   check_expression tenv (Position.value tyb) posb (Position.value b'');
	   let ty1, ty2 = arrow_type (Position.value tya) in

	   check_types posa (Position.value ty1) (Position.value tyb);
	   check_types pos xty (Position.value ty2) 
		       
	| IfThenElse (b, e1, e2) ->

	   (* - b => type bool
            - e1 => t1
            - e2 => t2
            - t1=t2 && t1=xty
	    *)

	   (* Test si b est bien du type bool *)
	   let b',pos_b = Position.destruct b in
	   let b'', tyb = undress_expression b' in
	   check_expression tenv (Position.value tyb) pos (Position.value b'');
	   check_types pos_b (Position.value tyb) (PrimitiveTypes.bool);

	   let e1', pos1 = Position.destruct e1 in
	   let e1'', ty1 = undress_expression e1' in
	   check_expression tenv (Position.value ty1) pos1 (Position.value e1'');
	   let e2', pos2 = Position.destruct e2 in
	   let e2'', ty2 = undress_expression e2' in
	   check_expression tenv (Position.value ty2) pos2 (Position.value e2'');
	   check_types pos xty (Position.value ty1);

	| Case (e, bl) ->
	   let e', pose = Position.destruct e in
	   let e'', ty1 = undress_expression e' in
	   check_expression tenv (Position.value ty1) pose (Position.value e'');
	   List.iter
	     (fun x ->
	      check_branch tenv (Position.value ty1) xty pos (Position.value x)) bl;
	   
	| TypeAnnotation (e, ty) -> 
           check_expression tenv (Position.value ty) pos (Position.value e)

	| Record (l) -> 
	   begin
	     match l with
             | [] -> type_error pos (Printf.sprintf "Empty record.")
             | (label,exp)::q -> 
		let list_types =
		  check_label_in_env (Position.value label) (List.length l) tenv pos in
		check_type_rec tenv pos l list_types
	   end
	| Field (e,lab) -> 

	   let e', pose = Position.destruct e in
	   let e'', ty1 = undress_expression e' in
	   check_expression tenv (Position.value ty1) pose (Position.value e'');
	   check_label_in_envS (Position.value lab) tenv pos
	| ChangeField (e1,lab,e2) -> 

	   (** e est de recorde *)
	   let e1', pose1 = Position.destruct e1 in
	   let e1'', ty1 = undress_expression e1' in
	   check_expression tenv (Position.value ty1) pose1 (Position.value e1'');

	   (** e2 est du meme type que lab  *)
	   let e2', pose2 = Position.destruct e2 in
	   let e2'', ty2 = undress_expression e2' in

	   (** et lab est dans l'environnement *)
	   let lab', pose3 = Position.destruct lab in
	   let tylabel = type_of_label_in_env lab' tenv pose3 in
	   check_types pos tylabel (Position.value ty2);
	   check_expression tenv (Position.value ty2) pose2 (Position.value e2'')


      and check_one_definerec tenv arg = 
	let (f, e) = arg in
	let e', pose = Position.destruct e in
	let e'', tye = undress_expression e' in
	check_expression tenv (Position.value tye) pose (Position.value e'')
			 
      and get_tenv_definerec tenv arg =
	let (f, e) = arg in
	let e', pose = Position.destruct e in
	let e'', tye = undress_expression e' in
	bind_definition tenv (Position.value f, Position.value tye)		       

      and check_branch tenv pty ety pos = function
	  Branch (patt, expr) ->
	  let patt', pospatt = Position.destruct patt in
	  let patt'', typatt = undress_pattern patt' in
	  let new_tenv =
	    check_pattern tenv
			  (Position.value typatt) pospatt (Position.value patt'')
	  in
	  
	  let expr', posexpr = Position.destruct expr in
	  let expr'', tyexpr = undress_expression expr' in
	  check_expression new_tenv
			   (Position.value tyexpr) posexpr (Position.value expr'');
	  
	  check_types pos pty (Position.value typatt);
	  check_types pos ety (Position.value tyexpr);
	  

      and literal tenv pos = function
	| LInt    _ ->
	   PrimitiveTypes.int
	| LString _ ->
	   PrimitiveTypes.string
	| LChar _ ->
	   PrimitiveTypes.char
	| LBool _ ->
	   PrimitiveTypes.bool
      in
      program tenv p

    (** [compute_expression_type tenv pos e] traverses [e] and tries
  to compute a type from the user type annotations and the
  shape of the input expression. *)

    and compute_expression_type tenv pos =
      failwith "Students, this is your job!"


    let make_fresh_type_variable  =
      let c = ref 0 in
      fun () -> incr c;
		TyVar (TId ("x" ^ string_of_int !c))

    (** [annotate p] completes [p] with enough type annotations to
      make it a fully annotated program. To generate a new type
      annotation, use [( make_fresh_type_variable () )] defined below. *)
    let annotate_literal l = match l with
      | LInt    _ ->
	 PrimitiveTypes.int
      | LString _ ->
	 PrimitiveTypes.string
      | LChar _ ->
	 PrimitiveTypes.char
      | LBool _ ->
	 PrimitiveTypes.bool


    let annote_term pos pos' e ty = 
      with_pos pos (TypeAnnotation( with_pos pos' e, ty))

    let annote_exp pos e ty = 
      with_pos pos (TypeAnnotation( with_pos pos e, ty))

    let annote_patt pos p ty = 
      with_pos pos (PTypeAnnotation ( with_pos pos p, ty))

    let rec annotate : program -> program = fun p ->
      let f = fun x ->  annotate_definition (Position.position x) (Position.value x) in
      List.map f p

    and annotate_definition pos = function
      | DeclareExtern(i,t) ->  
         with_pos pos (DeclareExtern(i,t))
      | DefineValue (x, e) ->
         let e' = (Position.value e) in 
         let pos' = (Position.position e) in
         with_pos pos (DefineValue (x,annotate_expression pos' e') )

      | DefineRecValue l ->
         with_pos pos ( 
		    DefineRecValue (
			(List.map (fun (f,x) ->
				   let x' = (Position.value x) in 
				   let pos' = (Position.position x) in
				   (f,annotate_expression pos' x') ) l)
		      ))
      | DefineType(a,b,c) -> with_pos pos (DefineType(a,b,c))

    and annotate_expression pos = function
      | Literal l ->
         let l' = (Position.value l) in 
         let pos' = (Position.position l) in
         let ty' = unknown_pos (annotate_literal l') in
         annote_term pos pos' (Literal l) ty'

      | Variable b -> 
         let ty' = unknown_pos ( make_fresh_type_variable () ) in
         annote_exp pos (Variable b) ty'
		    
      | Define (x, e1, e2) ->
         let e1' = (Position.value e1) in 
         let e2' = (Position.value e2) in 
         let pos1 = (Position.position e1) in
         let pos2 = (Position.position e2) in
         let ty' = unknown_pos ( make_fresh_type_variable () ) in
         annote_exp pos (
		      Define (x, (annotate_expression pos1 e1'),
			      (annotate_expression pos2 e2') )
		    ) ty'

      | DefineRec (l, e) ->
         let e' = (Position.value e) in 
         let pos = (Position.position e) in
         let ty' = unknown_pos ( make_fresh_type_variable () ) in
         annote_exp pos (
		      DefineRec (
			  (List.map (fun (f,x) ->
				     let x' = (Position.value x) in 
				     let pos' = (Position.position x) in
				     (f, annotate_expression pos' x') ) l),
			  annotate_expression pos e')
		    ) ty'

      | Apply (a, b) ->
         let a' = (Position.value a) in 
         let b' = (Position.value b) in 
         let pos1 = (Position.position a) in
         let pos2 = (Position.position b) in
         let ty' = unknown_pos ( make_fresh_type_variable () ) in
         annote_exp pos (
		      Apply ((annotate_expression pos1 a'),
			     (annotate_expression pos2 b') )
		    ) ty'
		    
      | IfThenElse (b, e1, e2) ->
         let b' = (Position.value b) in
         let e1' = (Position.value e1) in 
         let e2' = (Position.value e2) in 
         let posb = (Position.position b) in
         let pos1 = (Position.position e1) in
         let pos2 = (Position.position e2) in
         let ty' = unknown_pos ( make_fresh_type_variable () ) in
         annote_exp pos (
		      IfThenElse ((annotate_expression posb b'), 
				  (annotate_expression pos1 e1'),
				  (annotate_expression pos2 e2'))
		    ) ty'
      | Fun (p, e) ->
         let p' = (Position.value p) in 
         let e' = (Position.value e) in 
         let pos1 = (Position.position p) in
         let pos2 = (Position.position e) in
         let ty' =
	   unknown_pos
	     ( make_fresh_type_variable () --> make_fresh_type_variable () ) in
         annote_exp pos (
		      Fun ((annotate_pattern pos1 p'), (annotate_expression pos2 e') )
		    ) ty'
      | Tagged (k,le) ->
	 (* a revoir *)
         let ty' = unknown_pos ( make_fresh_type_variable () ) in
         let f = 
           fun x -> 
           annotate_expression (Position.position x) (Position.value x) in
         annote_exp pos (
		      Tagged (k , (List.map f le) )
		    ) ty'
		    
      | Case (e, lb) ->
         let e' = (Position.value e) in 
         let pos' = (Position.position e) in
         let ty' = unknown_pos ( make_fresh_type_variable () ) in
         annote_exp pos (
		      Case (
			  (annotate_expression pos' e'), 
			  (List.map 
			     (fun x ->
			      branch_annotated (Position.position x) (Position.value x)) 
			     lb)
			) 
		    ) ty'

      | Record r ->
         let ty' = unknown_pos ( make_fresh_type_variable () ) in
         annote_exp pos (
		      Record (
			  List.map 
			    (fun (x,e) ->
			     ( x,
			       annotate_expression
				 (Position.position e) (Position.value e)) 
			    ) r )
		    ) ty'
      | TypeAnnotation (p,ty)-> 
         with_pos pos (
		    TypeAnnotation (
			(annotate_expression
			   (Position.position p) (Position.value p)) ,ty)
		  )
      | Field(e, lab) ->
	 let e' = (Position.value e) in 
         let pos' = (Position.position e) in
         let ty' = unknown_pos ( make_fresh_type_variable () ) in
	 annote_exp pos (
		      Field (
			  (annotate_expression pos' e'), lab
			) 
		    ) ty'

      | ChangeField(e1, l, e2) -> 
	 let e1' = (Position.value e1) in 
         let pos1' = (Position.position e1) in
	 let e2' = (Position.value e2) in 
         let pos2' = (Position.position e2) in
         let ty' = unknown_pos ( make_fresh_type_variable () ) in
	 annote_exp pos (
		      ChangeField (
			  (annotate_expression pos1' e1'), l, (annotate_expression pos2' e2')
			) 
		    ) ty'

    and branch_annotated pos = function
      | Branch (p, e) ->
         let p' = (Position.value p) in 
         let e' = (Position.value e) in 
         let pos1 = (Position.position p) in
         let pos2 = (Position.position e) in
         with_pos pos (
		    Branch (annotate_pattern pos1 p',annotate_expression pos2 e') 
		  )

    and annotate_pattern pos = function
	
      | PRecord r ->
         let ty' = unknown_pos ( make_fresh_type_variable () ) in 
         annote_patt pos
		     (PRecord  (
			  List.map (fun (f,x) -> 
				    (f,annotate_pattern
					 (Position.position x) (Position.value x) )) r
			) ) ty'
      | POr l ->
         let ty' = unknown_pos ( make_fresh_type_variable () ) in 
         annote_patt pos (
  		       POr 
			 (List.map 
			    (fun x -> 
			     let x' = (Position.value x) in 
			     let pos' = (Position.position x) in 
			     annotate_pattern pos' x') 
			    l)
		     ) ty'

      | PAnd l ->
         let ty' = unknown_pos ( make_fresh_type_variable () ) in 
         annote_patt pos (
		       PAnd (List.map 
			       (fun x -> 
				let x' = (Position.value x) in 
				let pos' = (Position.position x) in 
				annotate_pattern pos' x') l)
		     ) ty'

      | PTaggedValue ( k , lp) ->
         let ty' = unknown_pos ( make_fresh_type_variable () ) in 
         annote_patt pos (
		       PTaggedValue( k ,
				     (List.map 
					(fun x -> 
					 let x' = (Position.value x) in 
					 let pos' = (Position.position x) in 
					 annotate_pattern pos' x') lp) 
				   )
		     ) ty'

      | PTypeAnnotation (p,ty)-> 
         with_pos pos (
		    PTypeAnnotation (
			(annotate_pattern (Position.position p) (Position.value p)) ,ty)
		  )
      | PLiteral l -> 
         let l' = (Position.value l) in 
         let ty' = unknown_pos (annotate_literal l') in
         annote_patt pos (PLiteral l) ty'

      | PWildcard -> 
         annote_patt pos (PWildcard)
		     (unknown_pos (make_fresh_type_variable ()) )

      | PVariable b -> 
         annote_patt pos (PVariable b) (unknown_pos (make_fresh_type_variable ()) )

		  
    (** A typing constraint is a conjunction of type equalities. *)
    type typing_constraint = (ty * ty) list


    let undress_expression' exp = match exp with
      | TypeAnnotation (e, ty) -> (Position.value e, Position.value ty)
      | _ ->(exp, ( make_fresh_type_variable () )) (* by is_fully_annotated. *)

    let undress_pattern' exp = match exp with
      | PTypeAnnotation (p, ty) -> (Position.value p,Position.value ty)
      | _ -> (exp, ( make_fresh_type_variable () )) (* by is_fully_annotated. *)

    let undress_label' tenv lab = 
      match types_of_label tenv lab with 
      | None -> assert false (* by is_well_formed. *)
      | Some (_,_,l) -> (List.assoc lab l)

    let undress_label_encaps' tenv lab =
      match types_of_label tenv lab with 
      | None -> assert false (* by is_well_formed. *)
      | Some (tc,_,_) -> TyCon(tc,[])

    (** [generate_constraint tenv p] takes a fully annotated program
       and generate typing constraints that are equivalent of
       its welltypedness. *)
    


    let rec generate_constraint_exp tenv tl cur = function
      | Literal l  -> (annotate_literal (Position.value l) ,cur)::tl

      | Variable v -> 
         ( idSome (lookup_value_type (Position.value v) tenv) , cur ) ::tl
									  
      | Define (x, e1, e2) ->
	 
         let e1', ty1' = undress_expression' (Position.value e1) in
         let e2', ty2' = undress_expression' (Position.value e2) in
	 let new_tenv = bind_value_type (Position.value x) (ty1') tenv in
         ((( make_fresh_type_variable () ), ty1')::(cur, ty2')::tl)@
           (generate_constraint_exp tenv [] ty1' e1')@
             (generate_constraint_exp new_tenv [] ty2' e2')
	       
      | DefineRec (l, e) ->
         let e', ty' = undress_expression' (Position.value e) in
	 let envB =  (List.fold_left (fun env (i,e)->
			    let e', ty' = undress_expression' (Position.value e) in
			    bind_value_type (Position.value i) (ty') env ) tenv l) in
         (cur, ty')::
           (List.fold_left (fun l1 (i,e)->
			    let e', ty' = undress_expression' (Position.value e) in
			    (( make_fresh_type_variable () ), ty')::
			      (generate_constraint_exp envB [] ty' e')@l1 ) [] l)@ 
	     (generate_constraint_exp envB [] ty' e')
      | Apply (a, b) ->
         let e1', ty1' = undress_expression' (Position.value a) in
         let e2', ty2' = undress_expression' (Position.value b) in
         ((ty1' , ty2' --> cur)::tl)@
           (generate_constraint_exp tenv [] ty1' e1')@
             (generate_constraint_exp tenv [] ty2' e2')

      | IfThenElse (b, e1, e2) ->
         let b', tyb' = undress_expression' (Position.value b) in
         let e1', ty1' = undress_expression' (Position.value e1) in
         let e2', ty2' = undress_expression' (Position.value e2) in
         ((tyb', PrimitiveTypes.bool)::(ty1', cur)::(ty2',cur )::tl)@
           (generate_constraint_exp tenv [] tyb' b')@
             (generate_constraint_exp tenv [] ty1' e1')@
               (generate_constraint_exp tenv [] ty2' e2')


      | Fun (p, e) ->
         let patt', typatt = undress_pattern' (Position.value p) in
         let e', ty' = undress_expression' (Position.value e) in
	 let new_tenv = check_pattern' tenv (typatt) (Position.position p) patt' in
         (( cur ,typatt --> ty')::tl)@
           (generate_constraint_pattern new_tenv [] typatt patt')@
	     (generate_constraint_exp new_tenv [] ty' e')

      | Tagged (k,le) -> 
	 let ltyp = type_of_constr (Position.value k) tenv in
	 let kons = (fst ltyp) in
	 let tyM = TyCon (kons, List.map unknown_pos [])  in
         (cur,tyM )::
         List.fold_left2
           (fun l e c -> 
            let e', ty' = undress_expression' (Position.value e) in
            (ty',c)::l@(generate_constraint_exp tenv [] ty' e') ) [] le (snd ltyp) 

      | TypeAnnotation (e, ty) ->
         let e', ty' = undress_expression' (Position.value e) in
         (((Position.value ty) , cur)::((Position.value ty) , ty')::tl)@
           (generate_constraint_exp tenv [] ty' e')

      | Case (e, lb) -> 
         let e', ty' = undress_expression' (Position.value e) in
         (List.fold_left
            (fun l { value = Branch (p, e1) } -> 
             let e1', ety' = undress_expression' (Position.value e1) in
             let p', pty' = undress_pattern' (Position.value p) in 
	     let new_tenv = check_pattern' tenv pty'
				           (Position.position p) p' in
	     (*Printf.printf " Bind %s \n " (print_typing_environment new_tenv);
	     Printf.printf "exp :  %s \n type : %s \n" (to_string expression (Position.value e1)) (to_string ty ety'); *)
             [(ty',pty'); (ety',cur)] @ 
               (generate_constraint_pattern new_tenv tl pty' p') @
		 (generate_constraint_exp new_tenv tl ety' e1') @ l ) [] lb)@
           generate_constraint_exp tenv [] ty' e'

      | Record r ->
	 let ltyp = type_of_label' (Position.value (fst (List.hd r)) ) tenv in
	 let kons = (fst ltyp) in
	 let tyM = TyCon (kons, List.map unknown_pos [])  in
         (cur,tyM)::
         (List.fold_left
            (fun l (a,b) -> 
             let e1', ety' = undress_expression' (Position.value b) in
             let lty' = undress_label' tenv (Position.value a) in
             (ety',lty'):: 
               (generate_constraint_exp tenv tl ety' e1')@ l ) [] r)
	   
      | Field (e,lab) -> 
         let e', ety' = undress_expression' (Position.value e) in
         let cty' = undress_label_encaps' tenv (Position.value lab) in
         let lty' = undress_label' tenv (Position.value lab) in
         [(cur,lty');(ety',cty')]@(generate_constraint_exp tenv tl ety' e')

      | ChangeField (e1,lab,e2) -> 
         let e1', e1ty' = undress_expression' (Position.value e1) in
         let e2', e2ty' = undress_expression' (Position.value e2) in
         let cty' = undress_label_encaps' tenv (Position.value lab) in
         let lty' = undress_label' tenv (Position.value lab) in
         [(e2ty',lty');(e1ty',cty');(PrimitiveTypes.unit,cur)]@
           (generate_constraint_exp tenv tl e1ty' e1')@
             (generate_constraint_exp tenv tl e2ty' e2') 
    and idSome a = match a with 
      | Some s -> s
      | None -> ( make_fresh_type_variable () )
  
    and generate_constraint_pattern tenv tl cur = function
	
      | PRecord r ->
	 let ltyp = type_of_label' (Position.value (fst (List.hd r)) ) tenv in
	 let kons = (fst ltyp) in
	 let tyM = TyCon (kons, List.map unknown_pos [])  in
         (cur,tyM)::(List.fold_left
		       (fun l (a,b) ->
			let lty1 = List.assoc (Position.value a) (snd ltyp) in
			let e1', ety' = undress_pattern' (Position.value b) in
			let lty' = undress_label' tenv (Position.value a) in
			(**Printf.printf "type %s %s %s" (to_string label (Position.value a)) (to_string ty lty') (to_string ty lty1); **)
			(ety',lty1)::(lty',lty1):: l ) [] r )

      | POr l -> 
         (List.fold_left
            (fun l a -> 
             let e1', ety' = undress_pattern' (Position.value a) in
             (ety',cur):: 
               (generate_constraint_pattern tenv [] ety' e1')@ l ) [] l)

      | PAnd l -> 
         (List.fold_left
            (fun l a -> 
             let e1', ety' = undress_pattern' (Position.value a) in
             (ety',cur):: 
               (generate_constraint_pattern tenv [] ety' e1')@ l ) [] l)

      | PTaggedValue (k , lb) -> 
         let ltyp = type_of_constr (Position.value k) tenv in
	 let kons = (fst ltyp) in
	 let tyM = TyCon (kons, List.map unknown_pos [])  in
         (cur,tyM )::(List.fold_left2
           (fun l e c -> 
            let e', ty' = undress_pattern' (Position.value e) in
	    (**Printf.printf "type %s %s %s" (to_string pattern e') (to_string ty ty') (to_string ty c); **)
            (ty',c)::
	      (generate_constraint_pattern tenv [] ty' e')@
	      l ) [] lb (snd ltyp))

      | PTypeAnnotation (p,ty)-> 
         let p', ty' = undress_pattern' (Position.value p) in
         (( (Position.value ty) , cur)::( (Position.value ty) , ty')::tl)@
           (generate_constraint_pattern tenv [] cur p')
             
      | PWildcard -> tl

      | PLiteral l -> 
         (annotate_literal (Position.value l),cur)::tl

      | PVariable v ->
	 let var = idSome (lookup_value_type (Position.value v) tenv) in
         ( var , cur ) :: tl

 
		      
    let rec generate_constraint_def tenv tl = function
      | DeclareExtern(i,t) -> (tl,tenv)
      | DefineValue (x, e) ->
         let e', ty' = undress_expression' (Position.value e) in
	 let tenv' = bind_value_type (Position.value x) ( ty') tenv in
         ((generate_constraint_exp tenv [] ty' e'),tenv')
      | DefineRecValue l   ->
	 let envB =  (List.fold_left (fun env (i,e)->
			    let e', ty' = undress_expression' (Position.value e) in
			    bind_value_type (Position.value i) (ty') env ) tenv l) in
         List.fold_left (fun (l1,tenv') (i,e)->
			 let e', ty = undress_expression' (Position.value e) in
			 (((generate_constraint_exp tenv' [] ty e')@l1),tenv') ) ([] ,envB) l

      | DefineType(tcon,ts,tdef)  ->
	 let new_tenv = bind_type_definition
			    (Position.value tcon)
			    (List.map Position.value ts)
			    tdef
			    tenv in
	 let env' =  bind_all_types ((Position.value tcon),(List.map Position.value ts)) new_tenv tdef in
	 (tl,env')   
									   
    let rec generate_constraint : typing_environment -> program -> typing_constraint =  fun tenv p ->
      let res = (List.fold_left
		   (
		     fun (l1,tenv') a ->
		    
		      let (l , env) = (generate_constraint_def tenv' [] (Position.value a) ) in 
		      (l@l1,env )
		   )
		   ([],tenv) p
		   
		) in
      (fst res)

    

    let string_of_constraint c =
     String.concat "; " (List.map (fun (t1, t2) ->
				    Printf.sprintf "%s =?= %s" (to_string ty t1) (to_string ty t2)
				   ) c)

    (** A type substitution maps type variable to types. *)
    type substitution = (type_variable, ty) Dict.t
    let string_of_substitution phi =
      String.concat "; " (List.map (fun (TId x, t) ->
				    Printf.sprintf "%s -> %s" x (to_string ty t)
				   ) (Dict.to_list phi))

    (** A type is ground if it does not contain any type variable. *)
    let rec ground_type pos = function
      | TyCon (_, tys) -> List.for_all (located ground_type) tys
      | _ -> false

    (** A substitution is ground if its image is only composed of
       ground types. *)
    let ground_substitution : substitution -> bool =
      fun phi ->
      Dict.to_list phi
      |> List.for_all (fun (_, ty) -> ground_type Position.dummy ty)

    (** [solve_constraint c] simplifies the typing constraint [c] and
      returns a substitution equivalent to [c] if [c] is
      satisfiable and has a unique ground solution. Otherwise, a
      type error message is issued.

      The solving process is based on first-order unification.
      (See: https://en.wikipedia.org/wiki/Unification_(computer_science))

      The first-order unification alg
      orithm rewrites the type
      equalities using 6 simplification rules (described below) as
      long as possible. Once finished, this rewriting process leads
      to three situations:

      1. The type equalities are of the form [âˆ§áµ¢ Xáµ¢ = Táµ¢],
         this form also encodes a substitution (which may or
         may not be ground).

         Also, âˆ€i j, Xáµ¢ âˆ‰ FV(Tâ±¼).

         (Be careful, this does not mean that the resulting substitution
          is ground...)

      2. The type equalities are inconsistent (written âŠ¥).
         (The program is ill-typed.)

      3. The type equalities contain a cycle.
         (The program is also ill-typed.)

      Here are the 6 simplification rules that must be used to
      simplify the initial constraint:

      - [delete]

                        c = (t, t) :: c' -> c'

        If an equality simply says that a type is equal to itself,
        it can be removed since it is not informative.

      - [decompose]

          c = (TyCon (a, tys1) = TyCon (a, tys2)) :: c' -> tys1 = tys2 @ c'

        Two types made from the same type constructors are equal if and
        only if their arguments are equal.

      - [conflict]

                c = (TyCon (a, tys1) = TyCon (b, tys2)) :: c' â€”â€”â€”â€“â†’ âŠ¥

        Two types made from distinct type constructors are equal is an
        inconsistency: the constraint is equivalent to âŠ¥.

      - [swap]

       c = (TyCon (a, ts) = TyVar x) :: c' â€”â€”â€”â€“â†’ (TyVar x = TyCon (a, ts) :: c'

        We orient equalities to have equalities of the form X = T in the end.

      - [eliminate]

                c = (TyVar x = t) :: c' â€”â€”â€”â€“â†’ (TyVar x = t) :: c' { TyVar x â†¦ t }

        Once we know that [x] is equal to [T], every occurence of [x] in other
        equalities can be removed.

       - [occur-check]

                c = (TyVar x = TyCon (a, ts)) :: c' â€”â€”â€”â€“â†’ âŠ¥     if x âˆˆ FV(ts)

        The equalities encode a cycle: the constraint is not
        satisfiable in the model of trees (and our types are syntactic
        representatives of this model).

      To implement the solver, you can either:

      - implement the 6 simplification rules and a function that goes
        through the list of equalities to apply them *in the right
        order*, you will get a naive but sound algorithm ;

      - or, you can implement a more sophisticated algorithm as described in
            Franz Baader and Tobias Nipkow,
            Term Rewriting and All That. Cambridge University Press, 1998.
        This algorithm is based on the UnionFind data structures and offers
        a linear complexity thanks to an optimisation of the [eliminate]
        simplification rule.

     *)
    let printType a = match a with
      |  TyVar x  -> Printf.printf "Var : %s\n !" (string_var x)
      | TyCon (x, _)  -> 
         Printf.printf "Constr : %s\n !" (string_constr x)

    let rec equal_ty a b = match a, b with
      | TyVar v, TyVar v' -> v = v'
      | TyCon (a, l), TyCon (b, l') when a = b ->
	 List.for_all2 (fun x y -> equal_ty (Position.value x)  (Position.value y)) l l'
      | _ -> false

    let delete c = 
      match c with
      | (a , b)::q when equal_ty a b -> q
      | _ -> c

    let rec decompose contrainte = 
      match contrainte with
      | [] -> []
      | (TyCon (a', tys1), TyCon (b', tys2) )::q 
	   when  a' = b' -> 
	 let ncst = 
	   (List.map2 (fun u v ->  ((Position.value u),(Position.value v)) )  tys1 tys2) in
	 ncst@(decompose q)
      | (TyCon (a', tys1), TyCon (b', tys2))::q 
	   when a' <> b' ->
	 Printf.printf "\n Salut :  %s =?= %s \n " (string_constr a') (string_constr b');
	 failwith "symbol clash !"
      | a::q -> a::(decompose q)

    let swap contrainte =
      match contrainte with
      | (TyCon (a, l), TyVar b ) ->
	 (TyVar b, TyCon (a, l))
      | _ -> contrainte

    let rec subst x t = function
      | TyVar x' as var ->
	 if x = x' then t
	 else var
      | TyCon (a, l) ->
	 (fun y ->
	  let y', pos = Position.destruct y in
	  let y'' = subst x t y' in
	  Position.with_pos pos y'')
	 |> (fun x -> List.map x l)
	 |> fun x -> TyCon (a, x)

    let rec eliminate contrainte =
      match contrainte with
      | [] -> []
      | (TyVar b,  t )::q -> 
	 let q = List.map 
		   (fun (x,y) -> (subst b t x ),(subst b t y) ) q in
	 (TyVar b, t):: (eliminate q) 
      | a::q ->  a::(eliminate q)

    let rec occurs_check' var = function
      | TyVar var' ->
	 var = var' 
      | TyCon (_, l) ->
	 List.exists (fun x -> occurs_check' var (Position.value x)) l

    let occurs_check contrainte = 
      match contrainte with 
      | ( (TyVar var) , TyCon (_, l) )->
	 if List.exists 
	      (fun x -> occurs_check' var (Position.value x) ) l
	 then failwith "occur-check"
	 else ()

      | _ ->()

    let rec foldsp (a,b) f = function
      | [] -> (a,b)
      | a'::q -> let ret = f ((a'::q),b) in
		foldsp ret f q
    let rec foldsp' (a,b) f = function
      | [] -> (a,b)
      | a'::q -> let ret = f (a'::q) b in
		foldsp' ret f q
		  
    let solve_constraint' cst=
      (** delete *)
      let cst' = List.filter (fun (a,b) -> not (equal_ty a b) ) cst in
     
      let cst'  = decompose cst' in
      
      let cst' = List.map (fun a ->  swap a)  cst' in
      
      let cst'  = (eliminate cst') in
      
      List.iter (occurs_check) cst';
      cst'

    let rec traiter c =
      (**Printf.printf "avant %s \n" (string_of_constraint c);**)
       let cs = 
	(List.sort (fun a b ->
			    match a,b with
			    |(TyVar a',ty),(TyVar b',ty') ->
			      if ground_type Position.dummy ty && ground_type Position.dummy ty' then
				0
			      else if ground_type Position.dummy ty && not (ground_type Position.dummy ty') then
				-1
			      else 1
			    | (TyVar a',_),(TyCon(a,l),_) ->
			       -1
			    | _ -> 0
						       
		   ) c) in
        
       
       let c' = solve_constraint' cs in
       (**Printf.printf "apres %s \n" (string_of_constraint c');**)
      if not (Dict.equal (Dict.of_list c) (Dict.of_list c') ) then 
	(traiter c')
      else c'

		 
    let solve_constraint contrainte  =
      
      let cst = traiter contrainte in
      List.map (fun (a,b) ->
		(match a with
		| TyVar a' -> (a',b)
		| _ -> assert false (**by unification algorithm *))
	       ) cst
      



    (** [elaborate phi p] takes a ground substitution [phi] and
      turns [p], a fully annotated program coming from the
      [annotate] function, into a program annotated only with
      ground types. *)
    let rec elaborate : substitution -> program -> program = fun phi p ->
      if ground_substitution phi then
	List.map 
	  (fun a -> 
           elaborate_def phi (Position.position a) (Position.value a) ) p
      else 
	failwith "not ground "

    and elaborate_def phi pos = function
      | DeclareExtern(i,t) ->  
         with_pos pos (DeclareExtern(i,t))

      | DefineValue (x, e) ->
         let e' = (Position.value e) in 
         let pos' = (Position.position e) in
         with_pos pos (DefineValue (x,elaborate_exp phi pos' e') )

      | DefineRecValue l ->
         with_pos pos ( 
		    DefineRecValue (
			(List.map (fun (f,x) ->
				   let x' = (Position.value x) in 
				   let pos' = (Position.position x) in
				   (f,elaborate_exp phi pos' x') ) l)
		      ))

      | DefineType(a,b,c) -> with_pos pos (DefineType(a,b,c))


    and elaborate_exp phi pos = function
      | Literal l ->
         with_pos pos (Literal l)

      | Variable b -> 
         with_pos pos (Variable b)
		  
      | Define (x, e1, e2) ->
         let e1' = (Position.value e1) in 
         let e2' = (Position.value e2) in 
         let pos1 = (Position.position e1) in
         let pos2 = (Position.position e2) in
         with_pos pos (
		    Define (x, (elaborate_exp phi pos1 e1'), (elaborate_exp phi pos2 e2') )
		  )
      | DefineRec (l, e) ->
         let e' = (Position.value e) in 
         let pos = (Position.position e) in
         with_pos pos (
		    DefineRec (
			(List.map (fun (f,x) ->
				   let x' = (Position.value x) in 
				   let pos' = (Position.position x) in
				   (f, elaborate_exp phi pos' x') ) l), elaborate_exp phi pos e')
		  )

      | Apply (a, b) ->
         let a' = (Position.value a) in 
         let b' = (Position.value b) in 
         let pos1 = (Position.position a) in
         let pos2 = (Position.position b) in
         with_pos pos (
		    Apply ((elaborate_exp phi pos1 a'), (elaborate_exp phi pos2 b') )
		  ) 
		  
      | IfThenElse (b, e1, e2) ->
         let b' = (Position.value b) in
         let e1' = (Position.value e1) in 
         let e2' = (Position.value e2) in 
         let posb = (Position.position b) in
         let pos1 = (Position.position e1) in
         let pos2 = (Position.position e2) in
         with_pos pos (
		    IfThenElse ((elaborate_exp phi posb b'), 
				(elaborate_exp phi pos1 e1'), (elaborate_exp phi pos2 e2'))
		  ) 
      | Fun (p, e) ->
         let p' = (Position.value p) in 
         let e' = (Position.value e) in 
         let pos1 = (Position.position p) in
         let pos2 = (Position.position e) in
         with_pos pos (
		    Fun ((elaborate_pattern phi pos1 p'), (elaborate_exp phi pos2 e') )
		  ) 
      | Tagged (k,le) ->
	 (* a revoir *)
         let f = 
           fun x -> 
           elaborate_exp phi (Position.position x) (Position.value x) in
         with_pos pos (
		    Tagged (k , (List.map f le) )
		  ) 
		  
      | Case (e, lb) ->
         let e' = (Position.value e) in 
         let pos' = (Position.position e) in
         with_pos pos (
		    Case (
			(elaborate_exp phi pos' e'), 
			(List.map 
			   (fun x -> elaborate_branch phi (Position.position x) (Position.value x)) 
			   lb)
		      ) 
		  ) 

      | Record r ->
         with_pos pos (
		    Record (
			List.map 
			  (fun (x,e) ->
			   ( x, elaborate_exp phi (Position.position e) (Position.value e)) 
			  ) r )
		  ) 
      | TypeAnnotation (p,ty)-> 
         with_pos pos (
		    TypeAnnotation (
			(elaborate_exp phi (Position.position p) (Position.value p)) ,
			with_pos pos ( (Position.value  ty) <-- phi ) )
		  )
       | Field(e, lab) ->
	 let e' = (Position.value e) in 
         let pos' = (Position.position e) in
         with_pos pos (
		      Field (
			  (elaborate_exp phi pos' e'), lab
			) 
		    )

      | ChangeField(e1, l, e2) -> 
	 let e1' = (Position.value e1) in 
         let pos1' = (Position.position e1) in
	 let e2' = (Position.value e2) in 
         let pos2' = (Position.position e2) in
         with_pos pos (
		      ChangeField (
			  (elaborate_exp phi pos1' e1'), l, (elaborate_exp phi pos2' e2')
			) 
		    ) 

    and elaborate_branch phi pos = function
      | Branch (p, e) ->
         let p' = (Position.value p) in 
         let e' = (Position.value e) in 
         let pos1 = (Position.position p) in
         let pos2 = (Position.position e) in
         with_pos pos (
		    Branch (elaborate_pattern phi pos1 p',elaborate_exp phi pos2 e') 
		  )
		  
    and elaborate_pattern phi pos = function
	
      | PRecord r ->
         with_pos pos
		  (PRecord  (
		       List.map (fun (f,x) -> 
				 (f,elaborate_pattern phi (Position.position x) (Position.value x) )) r
		     ) ) 
      | POr l ->
         with_pos pos (
		    POr 
		      (List.map 
			 (fun x -> 
			  let x' = (Position.value x) in 
			  let pos' = (Position.position x) in 
			  elaborate_pattern phi pos' x') 
			 l)
		  ) 

      | PAnd l ->
         with_pos pos (
		    PAnd (List.map 
			    (fun x -> 
			     let x' = (Position.value x) in 
			     let pos' = (Position.position x) in 
			     elaborate_pattern phi pos' x') l)
		  ) 

      | PTaggedValue ( k , lp) ->
         with_pos pos (
		    PTaggedValue( k ,
				  (List.map 
				     (fun x -> 
				      let x' = (Position.value x) in 
				      let pos' = (Position.position x) in 
				      elaborate_pattern phi pos' x') lp) 
				)
		  ) 

      | PTypeAnnotation (p,ty)-> 
         with_pos pos (
		    PTypeAnnotation (
			(elaborate_pattern phi (Position.position p) (Position.value p)) ,
			with_pos pos ( (Position.value  ty) <-- phi ) )
		  )
      | PLiteral l -> 
         with_pos pos (PLiteral l) 

      | PWildcard -> 
         with_pos pos (PWildcard)

      | PVariable b -> 
         with_pos pos (PVariable b)


    (** [infer tenv p] performs type inference on the program [p]. *)
    let infer tenv p =
      let p = annotate p in
      if Options.get_verbose_mode () then
	Printf.printf "[OK] Annotate:\n%s\n%!" (to_string program p);
      let c = generate_constraint tenv p in
      if Options.get_verbose_mode () then
	Printf.printf "[OK] Generated constraint:\n%s\n%!" (string_of_constraint c);
      let phi = Dict.of_list (solve_constraint c) in
      if Options.get_verbose_mode () then
	Printf.printf "[OK] Substitution:\n%s\n%!" (string_of_substitution phi);
      let p = elaborate phi p in
      if Options.get_verbose_mode () then
	Printf.printf "[OK] Elaboration:\n%s\n%!" (to_string program p);
      typecheck tenv p

  end

(** [typecheck tenv ast] checks that [ast] is a well-formed program
    under the typing environment [tenv]. *)
let typecheck tenv ast =
  if not (Options.get_check_types ()) then
    tenv
  else if Options.get_infer_types () then
    SimpleTypes.infer tenv ast
  else
    SimpleTypes.typecheck tenv ast

let print_typing_environment =
  HopixTypes.print_typing_environment
