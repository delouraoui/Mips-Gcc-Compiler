(** From Hopix to Hobix *)
open Position
module Source = Hopix
module Target = Hobix

(** The compilation environment.
    ———————————————————————————–

    To translate a program written in a source language into another
    semantically equivalent program written in a target language, it
    is convenient to carry some information about the correspondence
    between the two programs along the process. The compilation
    environment is meant to that.

    In this particular pass, we want to remember an assignment of
    integers to constructor and label identifiers. Therefore, the
    compilation environment is composed of two maps representing these
    assignments. The environment is populated each time we cross a
    type definitions while it is read each time we translate language
    constructions related to record and tagged values.
*)

module ConstructorMap = Map.Make (struct
  type t = HopixAST.constructor
  let compare = compare
end)

module LabelMap = Map.Make (struct
  type t = HopixAST.label
  let compare = compare
end)

type environment = {
  constructor_tags : Int32.t ConstructorMap.t;
  label_position   : Int32.t LabelMap.t
}

let initial_environment () = {
  constructor_tags = ConstructorMap.empty;
  label_position = LabelMap.empty
}


let index_of_constructor env k =
  ConstructorMap.find k env.constructor_tags

let index_of_label env l =
  LabelMap.find l env.label_position

let bind_constuctor env k i =
  let new_cm =
    ConstructorMap.add k i env.constructor_tags
  in
  {label_position=env.label_position;
      constructor_tags=new_cm}
  
let bind_label env l i =
  let new_lp =
    LabelMap.add l i env.label_position
  in {label_position=new_lp;
      constructor_tags=env.constructor_tags}
		 
(** Code generation
    ———————————————

    A compilation pass produces code. We could directly
    write down caml expressions made of applications of
    HobixAST constructors. Yet, the resulting code would
    be ugly...

    A better way consists in defining functions that build
    Hobix AST terms and are convenient to use. Here are a
    list of functions that may be convenient to you when
    you will implement this pass.

 *)

let fresh_int =
  let r = ref 0 in
  fun () -> incr r; Int32.of_int !r

				 
(** [fresh_identifier ()] returns a fresh identifier, that is
    an identifier that has never been seen before. *)
let fresh_identifier =
  let r = ref 0 in
  fun () -> incr r; HobixAST.Id ("_" ^ string_of_int !r)

(** [def w (fun x -> e)] returns an abstract syntax tree of
    the form:

    val x = w; e

    where [x] is chosen fresh.
*)
let def w f =
  let x = fresh_identifier () in
  HobixAST.Define (x, w, f x)

(** [defines [d1; ..; dN] e] returns an abstract syntax tree of
    the form:

    val d1;
    ..
    val dN;
    e

 *)
				  
let defines =
  List.fold_right (fun (x, xe) e -> HobixAST.Define (x, xe, e))

(** [seq s1 s2] is

    val _ = s1;
    s2

*)
let seq s1 s2 =
  HobixAST.Define (fresh_identifier (), s1, s2)

(** [seqs [s1; ...; sN] is

    val _ = s1;
    ...
    val _ = s(N - 1);
    sN
*)
let rec seqs = function
  | [] -> assert false
  | [e] -> e
  | e :: es -> seq e (seqs es)

let rec seqs2 e = function
  | [] -> e
  | (x,e')::tl -> HobixAST.Define (x,e', seqs2 e tl)

(** util *)
let undress_branch br =
  let (HopixAST.Branch (p,e)) = Position.value br in
  (p,e)

let literal_of_int i = HobixAST.(
    i
    |> Int32.of_int
    |> (fun x -> LInt x)
    |> (fun x -> Literal x))

let literal_of_int32 i = HobixAST.(
    i
    |> (fun x -> LInt x)
    |> (fun x -> Literal x))

let read_block a x =
  HobixAST.ReadBlock (a,x)

let alloc i = HobixAST.(i
    |> Int32.of_int
    |> (fun x -> LInt x)
    |> (fun x -> Literal x)
    |> (fun x -> AllocateBlock x))
    
let write_block a i e = HobixAST.(
    WriteBlock
      (Variable a,i
      |> Int32.of_int
      |> (fun x -> LInt x)
      |> (fun x -> Literal x),
       e))
(** *)
			       
			       
module type LISTMONAD =
  sig
    type 'a t = 'a list
    exception Failed
    val return : 'a -> 'a t
    val ( >>= ) : 'a t -> ('a -> 'b t) -> 'b t
    val run : 'a t -> 'a
    val runall : 'a -> 'a
    val fail : 'a t
    val either : 'a t -> 'a t -> 'a t
  end

module ListMonad : LISTMONAD =
  struct
    type 'a t = 'a list
    exception Failed
    let return a = [a]
    let ( >>= ) a f = List.(map f a |> flatten)
    let run m = match m with
	hd :: tl -> hd | _ -> raise Failed
    let runall m = m
    let fail = []
    let either a b = a @ b
  end

open ListMonad

       
let preprocess p =

  let rec program p =
    List.map (fun x -> unknown_pos (definition (value x))) p

  and definition = HopixAST.(
      function
      | DeclareExtern (a,b) ->
	 DeclareExtern (a,b)
		       
      | DefineValue (x, e) ->
	 DefineValue (x, unknown_pos (expression (value e)))
		     
      | DefineRecValue recs ->
	 DefineRecValue (List.map (fun (a,b) -> (a, unknown_pos (expression (value b)))) recs)
			
      | DefineType _ as tdef -> tdef)
			   
  and expression = HopixAST.(
      function
      | Literal _ as lit -> lit
      | Variable _ as var -> var
      | Define (x,e1,e2) ->
	 let e1' = expression (value e1) |> unknown_pos in
	 let e2' = expression (value e2) |> unknown_pos in
	 Define (x, e1', e2')
		
      | DefineRec (le, e) ->
	 let le' = List.map (fun (a,b) -> (a, unknown_pos (expression (value b)))) le in
	 let e' = expression (value e) |> unknown_pos in
	 DefineRec (le', e')
	 
      | Apply (a,b) ->
	 let a' = expression (value a) |> unknown_pos in
	 let b' = expression (value b) |> unknown_pos in
	 Apply (a', b')
	       
      | IfThenElse (b, t, f) ->
	 let b' = expression (value b) |> unknown_pos in
	 let t' = expression (value t) |> unknown_pos in
	 let f' = expression (value f) |> unknown_pos in
	 IfThenElse (b', t', f')
	 	 
      | Fun (p, e) ->
	 let p' = pattern (value p) |> unknown_pos in
	 let e' = expression (value e) |> unknown_pos in
	 Fun (p', e')

      | Tagged (k, le) ->
	 let le' = List.map (fun x -> expression (value x) |> unknown_pos) le in
	 Tagged (k ,le')
		
      | Case (e, bl) ->
	 let e' = expression (value e) |> unknown_pos in
	 let bl' = List.map (fun x -> branch (value x) |> unknown_pos) bl in
	 Case (e', bl')
	 
      | TypeAnnotation (e, ty) ->
	 expression (value e)
		    
      | Record le ->
	 let le' = List.map (fun (a,b) -> a, expression (value b) |> unknown_pos) le in
	 Record le'
	 
      | Field (e, l) ->
	 let e' = expression (value e) |> unknown_pos in
	Field (e', l)	 

      | ChangeField (e1, l, e2) ->
	 let e1' = expression (value e1) |> unknown_pos in
	 let e2' = expression (value e2) |> unknown_pos in
	 ChangeField (e1', l ,e2'))

  and pattern = HopixAST.(
      function
      | PTypeAnnotation (p, ty) ->
	 pattern (value p)
		 
      | PVariable _ as pvar -> pvar
				 
      | PTaggedValue (k, pl) ->
	 let pl' = List.map (fun x -> pattern (value x) |> unknown_pos) pl in
	 PTaggedValue (k, pl')
		      
      | PWildcard as pw -> pw 
      | PLiteral _ as plit -> plit
				
      | PRecord prl ->
	 let prl' = List.map (fun (a,b) -> a, pattern (value b) |> unknown_pos) prl in
	 PRecord prl'
	     
      | POr pl ->
	 let pl' = List.map (fun x -> pattern (value x) |> unknown_pos) pl in
	 POr pl'
	     
      | PAnd pl ->
	 let pl' = List.map (fun x -> pattern (value x) |> unknown_pos) pl in
	 PAnd pl')

  and branch = HopixAST.(
      function
      | Branch (p, e) ->
	 let p' = pattern (value p) |> unknown_pos in
	 let e' = expression (value e) |> unknown_pos in
	 Branch (p', e'))

  in

  program p
  
				      
(** [program env p] turns an Hopix program into an equivalent
    Hobix program. *)
let rec program env p =
  let env, defs = ExtStd.List.foldmap definition' env p in
  (List.flatten defs, env)

(** Compilation of Hopix toplevel definitions. *)
and definition' env p =
  definition env (Position.value p)

and definition env = HobixAST.(function
  | HopixAST.DeclareExtern (x, _) ->
    env, [DeclareExtern (located identifier x)]

  | HopixAST.DefineValue (x, e) ->
    env, [DefineValue (located identifier x, located (expression env) e)]

  | HopixAST.DefineRecValue recs ->
    env, [DefineRecValue (List.map (value_definition env) recs)]

  | HopixAST.DefineType (_, _, tydef) ->
    type_definition env tydef, []
)

and value_definition env (x, e) =
  (located identifier x, located (expression env) e)

and identifier (HopixAST.Id x) =
  HobixAST.Id x

	      
(** Compilation of Hopix expressions. *)
and expression env = HobixAST.(function
  | HopixAST.Variable x ->
    Variable (located identifier x)   
	     
  | HopixAST.Apply (e1, e2) ->
    Apply (located (expression env) e1,
	   located (expression env) e2)

  | HopixAST.Literal l ->
    Literal (located literal l)

  | HopixAST.Define (x, e1, e2) ->
    Define (located identifier x,
	    located (expression env) e1,
	    located (expression env) e2)

  | HopixAST.DefineRec (recs, e) ->
    DefineRec (List.map (value_definition env) recs,
 	       located (expression env) e)

  | HopixAST.TypeAnnotation (e, ty) ->
    located (expression env) e

  | HopixAST.IfThenElse (e1, e2, e3) ->
    IfThenElse (located (expression env) e1,
		located (expression env) e2,
		located (expression env) e3)

  | HopixAST.Tagged(k, l) ->

     let pos = ref 0 in
     let index = index_of_constructor env (value k) in

     let f1 () =
       fun x y ->
       incr pos;
       write_block x !pos (expression env (value y))
     in
     
     let f2 = fun x ->
       write_block x 0 (literal_of_int32 index)
       :: List.map (f1 () x) l @ [Variable x] |> seqs in
   
     def (alloc (1 + List.length l)) f2

  | HopixAST.Fun(p,e) ->

     let fresh_var =
       fresh_int ()
       |> Int32.to_int
       |> string_of_int
       |> (fun x -> "__" ^ x)
     in
     let x =
       HopixAST.Id fresh_var
       |> unknown_pos
       |> (fun x -> HopixAST.Variable x)
       |> unknown_pos
     in
     
     let case =
       HopixAST.Case (x, [unknown_pos (HopixAST.Branch (p,e))])
     in
     
     let new_e = expression env case in
     HobixAST.Fun (HobixAST.Id fresh_var, new_e)
		
  | HopixAST.Record l ->
     def (l |> List.length |> alloc)
	 ((fun x -> List.map
		     (fun (a,b) ->
		      write_block x
				  (LabelMap.find (value a) env.label_position |> Int32.to_int)
				  (value b |> expression env)) l @ [Variable x]|> seqs))

  | HopixAST.Field (e, l) ->
     let mem=
       Position.value e |> expression env
     in
     let pos =
       LabelMap.find (Position.value l) env.label_position
     in
     ReadBlock (mem, Literal (LInt (pos)))

  | HopixAST.ChangeField (e, l, e') ->
     let mem=
       Position.value e |> expression env
     in
     let e''=
       Position.value e' |> expression env
     in
     let pos =
       LabelMap.find (Position.value l) env.label_position
     in
     WriteBlock (mem, Literal (LInt pos), e'')

  | HopixAST.Case (e, lb) ->
     let e' = expression env (Position.value e) in
     let new_lb = expands_or_branches lb in
     change_if env e' new_lb
)

			     
(** change_if env e' l transforme la liste de pattern 
    en une suite d'instruction IfThenElse *)
and change_if env e' = HobixAST.(function

  (* cas impossible *)
  | [] -> assert false

  (* cas ou on est dans le dernier pattern *)
  | (patt,expr)::[] ->
     
     let (ds,_) = pattern env e' (value patt) in
     seqs2 (expression env (value expr)) ds

  (* on parcours la liste de pattern expression *)
  | (patt,expr)::tl ->

     let (ds,cond) = pattern env e' (value patt) in
     begin
       
       match cond with

       (* cas ou la condition vaut true *)
       | Literal (LBool true) ->
	  seqs2 (expression env (value expr)) ds

       (* sinon *)
       | _ ->
	  IfThenElse (cond,
		      seqs2 (expression env (value expr)) ds,
		      change_if env e' tl)
		     
     end)
     

	

(** [expands_or_patterns branches] returns a sequence of branches
    equivalent to [branches] except that their patterns do not contain
    any disjunction. {ListMonad} can be useful to implement this
    transformation. *)

			      

and expands_or_branches lb =
  List.map undress_branch lb
  |> expands_or_patterns   
  
and expands_or_patterns branches = 
  branches >>= fun (p,e) ->
  expanse p >>= fun p' ->
  return (p',e)
 
and expanse a = HopixAST.(
    let (a', posa) = destruct a in
    match a' with
      
    (* Terminal term *)
    | (PLiteral _ | PWildcard | PVariable _) ->
       return a
    (***)
	      
    | POr ps ->
       expanse_patterns ps >>= fun ps ->
       ps >>= fun p ->
       return p
	      
    | PTaggedValue (k, ps) ->
       expanse_patterns ps >>= fun ps ->
       PTaggedValue (k, ps)
       |> Position.with_pos posa
       |> return 
	      
    | PRecord ps ->
       expanse_tuples ps >>= fun ps ->
       PRecord ps
       |> Position.with_pos posa
       |> return
	      
    | PTypeAnnotation (p, ty) ->
       expanse p >>= fun p ->
       PTypeAnnotation (p, ty)
       |> Position.with_pos posa
       |> return
	      
    | PAnd ps ->
       expanse_patterns ps >>= fun ps ->
       PAnd ps
       |> Position.with_pos posa
       |> return)
	    
and expanse_patterns = function
    | [] -> return []
    | p :: ps ->
       expanse p >>= fun p ->
       expanse_patterns ps >>= fun ps ->
       return (p :: ps)
		 
and expanse_tuples = function
  | [] -> return []
  | (a, p):: ps ->
     expanse p >>= fun p ->
     expanse_tuples ps >>= fun ps ->
     return ( (a,p) :: ps )
		  
		  


(** [pattern env scrutinee p] returns a boolean condition [c]
    and a list of definitions [ds] such that:

    - [c = true]Position.with_pos posa if and only if [p] matches the [scrutinee] ;
    - [ds] binds all the variables that appear in [p].

*)
and pattern env scrutinee p = HobixAST.(
    match scrutinee, p with

    | _, HopixAST.PWildcard ->
       [], Literal (LBool true)

    | _, HopixAST.PTaggedValue (k, largs) ->

       let index =
	 value k
	 |> index_of_constructor env
	 |> literal_of_int32
       in

       let readblock =
	 literal_of_int 0 |> read_block scrutinee
       in
       
       let bin = binop env "`=" readblock index in
	     
       if largs = [] then [], bin else
	 
	 let i = ref 0 in
	 let patt =
	   fun x ->
	   incr i ;
	   pattern env 
		   (literal_of_int !i |> read_block scrutinee)
		   (Position.value x)
	 in
	 
	 let largs' = largs >>= fun x -> return (patt x) in
	 
	 let ds = largs' >>= fun (x,_) -> x in
	 let lcond = largs' >>= fun (_,y) -> return y in
	 
	 ds, IfThenElse (bin,
			 List.(fold_left
				 (binop env "`&&")
				 (hd lcond) (tl lcond)),
			 Literal (LBool false))
			
    | _, HopixAST.PLiteral l ->
       [], Literal (Position.value l |> literal)
	   |> binop env "`=" scrutinee
						       
    | _, HopixAST.PVariable v ->
       [Position.value v |> identifier, scrutinee], Literal (LBool true)
							    
    | Literal _, _ ->
       [], Literal (LBool false)
		   
    | _ -> assert false
)


and binop env b x y  =
  let b = unknown_pos b in
  let op = map (fun x -> HopixAST.Variable (map (fun _ -> HopixAST.Id x) b)) b in
  HobixAST.(Apply (Apply (expression env (value op),x), y))

  
and literal = HobixAST.(function
  | HopixAST.LInt x -> LInt x
  | HopixAST.LString s -> LString s
  | HopixAST.LChar c -> LChar c
  | HopixAST.LBool b -> LBool b
)
			   
(** Compilation of type definitions. *)
and type_definition env = HopixAST.(function
  | Abstract -> env
  | DefineSumType l ->
     List.fold_left
       (fun env' (k',_) ->
	bind_constuctor env' (Position.value k') (fresh_int ()))
       env l
       
  | DefineRecordType l ->
     let r= ref (-1) in
     List.fold_left
       (fun env' (l',_) ->
	bind_label env' (Position.value l') (r := !r+1; Int32.of_int !r))
       env l)
			  
(** Here is the compiler! *)
let translate source env =
  let source' = preprocess source in
  program env source'
