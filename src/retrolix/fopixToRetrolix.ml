(** This module implements a compiler from Fopix to Retrolix. *)
open GraphColoring
let error pos msg =
  Error.error "compilation" pos msg

(** As in any module that implements {!Compilers.Compiler}, the source
    language and the target language must be specified. *)
module Source = Fopix
module Target = Retrolix
module S = Source.AST
module T = Target.AST

(** We will need the following pieces of information to be carrying
    along the translation: *)
module IdCmp = struct
    type t = T.identifier
    let compare = compare
  end
module IdSet = Set.Make (IdCmp)

(** The compilation environment stores the list of global
    variables (to compute local variables) and a table
    representing a renaming (for alpha-conversion). *)
type environment = IdSet.t * (S.identifier * S.identifier) list

(** Initially, the environment is empty. *)
let initial_environment () = (IdSet.empty, [])

(** [fresh_label ()] returns a new identifier for a label. *)
let fresh_label =
  let c = ref 0 in
  fun () -> incr c; T.Label ("l" ^ string_of_int !c)

(** [fresh_label ()] returns a new identifier for a variable. *)
let fresh_variable =
  let c = ref 0 in
  fun () -> incr c; T.(Id ("X" ^ string_of_int !c))

let fresh_variableS =
  let c = ref 0 in
  fun () -> incr c; (("N" ^ string_of_int !c))
(**
   Every function in Retrolix starts with a declaration
   of local variables. So we need a way to compute the
   local variables of some generated code. This is the
   purpose of the next function:
 *)

let set_label i = function
  | T.Label s ->
     T.Label ("l"^(string_of_int (int_of_string (String.sub s 1 ((String.length s)-1) ) + i)))
  
let give_var l globals = function
  | `Variable x ->
     if not (IdSet.mem x globals) && not (List.mem x l) then
       [x]
     else []
  | _ -> []

let l_of_rv l globals =function 
  | `Immediate _ -> []
  | lv' -> (give_var l globals lv')
	     
let give_vars l rvl globals =
  (List.map (l_of_rv l globals) rvl )
    
let construct_locals l lv rvl globals = 
  (List.flatten (give_vars l rvl globals))@(give_var l globals lv)

let rec extract_loc_var l' l globals = function
  | T.Call (lv, rv , rvl) ->
     (construct_locals l' lv rvl globals)@(l_of_rv l' globals rv)@l
  | T.TailCall (rv,rvl) ->
     (List.flatten (give_vars l' rvl globals))@(l_of_rv l' globals rv)@l
  | T.Ret(rv) ->
     (l_of_rv l' globals rv)@l
  | T.Assign(lv,op,rvl) ->
     (construct_locals l' lv rvl globals)@l
  | T.Jump (lab) ->
     l
  | T.ConditionalJump (cd, rvl,_,_) ->
     (List.flatten (give_vars l' rvl globals))@l
  | T.Switch (rv, _ , _) ->
     (l_of_rv l' globals rv)@l
  | T.Comment(str) ->
     l
  | T.Exit ->
     l

       
(** [locals globals b] takes a set of variables [globals] and returns
    the variables use in the list of instructions [b] which are not
    in [globals]. *)
       
let locals globals b =
  List.fold_left (fun l instr ->
		  (extract_loc_var l [] (globals) (snd instr))@l) [] b

(** [translate' p env] turns a Fopix program [p] into a Retrolix
    program using [env] to retrieve contextual information. *)
let rec translate' p env =
  (** The global variables are extracted in a first pass. *)
  let (globals, renaming) = env in
  let globals = List.fold_left get_globals globals p in
  let env = (globals, renaming) in
  (** Then, we translate Fopix declarations into Retrolix declarations. *)
  let defs = List.map (declaration globals) p in
  (defs, env)

and identifier (S.Id x) = T.Id x

and get_globals env = function
  | S.DefineValue (x, _) ->
     push env x
  | _ ->
     env

and push env x =
  IdSet.add (identifier x) env
and convention_t t acc1 acc2 =
  T.(function
  | -1 -> (List.rev acc1),( acc2)
  | k ->
     let variable =  fresh_variable () in 
    (convention_t t ( (labelled (Assign (`Variable variable, Load, [ `Register (RId (t^(string_of_int k)) )  ])))
     ::acc1) ((`Variable variable)::acc2) (k-1))
  )
and convention_e t l =
  T.(function
  | -1 -> []
  | k ->
     labelled (Assign ( `Register (RId (t^(string_of_int k)) ) , Load, [(List.nth l k) ]))::(convention_e t l (k-1))
  )  
and convention_start t i k =
  T.(function
  | [] -> []
  | a::q when k<=i->
     let variable =  fresh_variable () in 
     labelled (Assign (`Variable variable, Load, [ `Register (RId (t^(string_of_int k)) )  ]))::(convention_start t i (k+1) q)
  | a::q when k > i ->
     []
  | l -> [])
and convention_end t i k =
  T.(function
  | [] -> []
  | a::q when k<=i->
     let variable =  fresh_variable () in 
     labelled (Assign (`Register (RId (t^(string_of_int k)) ) , Load, [ `Variable variable ]))::(convention_end t i (k+1) q)
  | a::q when k > i ->
     []
  | l -> [])

and load_args i = function
  |[] -> []
  | a::q when i <= 3 ->
     [labelled (
	 T.Assign ( (`Variable a ),T.Load,[(`Register (T.RId ("$a"^(string_of_int i)) ))]))]@
       (load_args (i+1) q)

  | a ::q ->
     let x = fresh_variable () in 
     [labelled (
	 T.Assign ( (`Variable a ),T.Load,[(`Variable x )]))]@
       (load_args (i+1) q)
       
and declaration env =
  T.(function
      | S.DefineValue (S.Id x, e) ->
	 let x = Id x in
	 let ec = expression (`Variable x) e in
	 let local = locals env ec in
	 DValue (x, (local, ec))

      | S.DefineFunction (S.FunId f, xs, e) ->
	 let x = fresh_variable () in
	 let ec = expression (`Variable x) e in
	 let xs = List.map identifier xs in
	 let loc = locals env (ec) in
	 let loc = List.filter (fun x -> not (List.mem x xs) ) loc in
	 let loc = List.filter (fun x -> not((fun (Id y) -> y)x = f) ) loc in
	 DFunction (FId f,
		    xs,
		    (loc,load_args 0 xs @
		     ec @ [labelled (Ret (`Variable x))] ))
      | S.ExternalFunction (S.FunId f) ->
	 DExternalFunction (FId f)
  )

and conv es out =

  let argsT,vl = convention_t "$t" [] [] 9 in
  let argsE = convention_e "$t" vl 9 in
  let argSt = convention_start "$a" 3 0 es in
  let argSE = convention_end "$a" 3 0 es in
  (** On sauvegarde ra dans fp .... :/*)
  let x = fresh_variable () in
  let x1 = fresh_variable () in
  (** On sauvegarde ra dans fp .... :/*)
  let ret1 =[labelled (T.Assign ( ((`Variable x1 )  ),T.Load,[(`Register (T.RId "$ra") )]) );
       (** regle le pb des adresse bizare*)
       labelled (T.Assign ( (`Variable x ),T.Load,[(`Register (T.RId "$fp") )]) )
      ] in
  let ret2 = [
      labelled (T.Assign ( (`Register (T.RId "$fp") ),T.Load, [(`Variable x )] ));
      labelled (T.Assign ( (`Register (T.RId "$ra") ),T.Load, [((`Variable x1 ) )] ))
         (** regle le pb des adresse bizare*)
        
       ] in
  (argsT,argSt,ret1,argsE,argSE,ret2)
     
(** [expression out e] compiles [e] into a block of Retrolix
    instructions that stores the evaluation of [e] into [out]. *)
and expression out =
  T.(function
      | S.Literal l ->
	 [labelled (Assign (out, Load, [ `Immediate (literal l) ]))]

      | S.Variable (S.Id x) ->
	 [labelled (Assign (out, Load, [ `Variable (Id x) ]))]

      | S.Define (S.Id x, e1, e2) ->
	 
	 expression (`Variable (Id x)) e1 @ expression out e2

      | S.IfThenElse (c, t, f) ->
	 let c = (match c with
	 | S.Literal (S.LBool true) ->
	    S.FunCall (S.FunId "`=", [ S.Literal (S.LInt (Int32.of_int 0));S.Literal (S.LInt (Int32.of_int 0))] )
	 |  S.Literal (S.LBool false) ->
	     S.FunCall (S.FunId "`=", [ S.Literal (S.LInt (Int32.of_int 1));S.Literal (S.LInt (Int32.of_int 0))] )
	 | _ -> c
		 ) in
	 let x = fresh_variable () in
	 let x1 = fresh_variable () in
	 let cond = expression (`Variable x) c in
	 let labcond = fresh_label () in 
	 let t' = expression (`Variable x1) t in
	 let labjump = fresh_label () in  
	 let f' = expression (`Variable x1) f in
	 let lt = first_label t' in
	 let lf = first_label f' in
	 let racord = fresh_label () in
	 let setjump =  [(labjump,Jump (racord))] in
	 let  jumpIf = condition lt lf x labcond in
	 cond@jumpIf@t'@setjump@ f'@[(racord,T.Assign (out, Load, [(`Variable x1)])) ]

      | S.FunCall (S.FunId "allocate_block", es ) ->
	 let (at,ast,ret1,ae,fet,ret2) = conv es out in
	 at @ ast @ ret1 @

	 assign out BlockCreate (es) @
	  ret2 @ fet  @ ae
      | S.FunCall (S.FunId "read_block", es) ->
	  let (at,ast,ret1,ae,fet,ret2) = conv es out in
	 at @ ast @ ret1 @
	 assign out BlockGet es @
	   ret2 @ fet  @ ae
      | S.FunCall (S.FunId "write_block", es) ->
         let (at,ast,ret1,ae,fet,ret2)= conv es out in
	 at @ ast @ ret1 @
	 assign out BlockSet es @
	  ret2 @ fet  @ ae
      | S.FunCall (S.FunId f, es) when is_binop f ->
	 assign out (binop f) es 

      | S.FunCall (S.FunId f, actuals) ->
	 let (at,ast,ret1,ae,fet,ret2) = conv actuals out in 
	  at @ ast @ ret1@
	    call out (`Immediate  (LFun (FId f))) (actuals) @
	   ret2 @ fet  @ ae

      | S.UnknownFunCall (ef, actuals) ->
	 let rv, exp = (as_rvalue ef) in
	   exp@call out rv (actuals) 
	 
      | S.Switch (e, cases, default) ->
	 failwith "3 Students! This is your job!"
  )


and as_rvalue e =
  let x = `Variable (fresh_variable ()) in
  (x, expression x e)

and as_rvalues rs f =
  let xs, es = List.(split  (map as_rvalue rs)) in
  List.flatten es @ f xs

and assign out op rs =
  as_rvalues rs (fun xs ->
		 [labelled (T.Assign (out, op, xs))]
		)
and call out op rs =
  as_rvalues rs (fun xs ->
		 [labelled (T.Call (out, op, xs))]
		)

and condition lt lf x lab = T.(    
    [ (lab ,ConditionalJump (EQ, [ `Variable x;
					 `Immediate (LInt (Int32.of_int 0)) ],
                                   lf,
                                   lt))]
			)

and first_label = function
  | [] -> assert false
  | (l, _) :: _ -> l

and labelled i =
  (fresh_label (), i)

and literal =
  T.(function
      | S.LInt x ->
	 LInt x
      | S.LFun (S.FunId f) ->
	 LFun (FId f)
      | S.LChar c ->
	 LChar c
      | S.LString s ->
	 LString s
      | S.LBool b ->
	 LBool b
  )

and is_binop = function
  | "`+" | "`-" | "`*" | "`/" -> true
  | c -> is_condition c

and is_condition = function
  | "`<" | "`>" | "`=" | "`<=" | "`>=" -> true
  | _ -> false

and binop =
  T.(function
      | "`+" -> Add
      | "`-" -> Sub
      | "`*" -> Mul
      | "`/" -> Div
      | c -> Bool (condition_op c)
  )

and condition_op =
  T.(function
      | "`<" -> LT
      | "`>" -> GT
      | "`<=" -> LTE
      | "`>=" -> GTE
      | "`=" -> EQ
      | "`&&" -> AND
      | "`||" -> OR
      | _ -> assert false
  )

type ('a , 'b) runtime = ('a * 'b) list

let rec bind k = function
  | [] -> [ (k, k) ]
  | (k', v') :: tl when k = k' ->
     (k, fresh_variableS ()) :: (k, v') :: tl
  | c :: tl ->
     c :: bind k tl


let lookup k env = List.assoc k env  
let preprocess p =

  let rec ldefinition env = function
    | S.DefineValue (S.Id x, e) :: tl ->
       let env' = bind x env in
       let x' = lookup x env' in
       S.DefineValue (S.Id x', analyse env' e)
       :: ldefinition env' tl
	 
    | S.DefineFunction (S.FunId f, xs, e) :: tl ->
       let e' = analyse env e in
       S.DefineFunction (S.FunId f, xs, e')
       :: ldefinition env tl
			
    | S.ExternalFunction (S.FunId f) :: tl ->
       S.ExternalFunction (S.FunId f)
       :: ldefinition env tl
			  
    | [] -> []

  and subst e x e' = match e with

    (* literal *)
    | S.Literal l -> S.Literal l 

    (* substitution *)
    | S.Variable (S.Id x') when x = x' ->
       S.Variable (S.Id e')

    (* variable *)
    | S.Variable (S.Id x')  ->
       S.Variable (S.Id x')

    (* define *)
    | S.Define (S.Id x', e1, e2) ->
       S.Define (S.Id x',  (subst e1 x e'),  (subst e2 x e') )

    (* if then else *)
    | S.IfThenElse (c, t, f) ->
       S.IfThenElse ((subst c x e'),  (subst t x e'), (subst f x e') ) 

    (* allocate *)
    | S.FunCall (S.FunId "allocate_block", es) ->
       S.FunCall (S.FunId "allocate_block", es)
		 
    | S.FunCall (S.FunId "read_block", es) ->
       S.FunCall (S.FunId "read_block",  (List.map (fun y -> subst y x e') es))
		 
    | S.FunCall (S.FunId "write_block", es) ->
       S.FunCall (S.FunId "write_block",  (List.map (fun y -> subst y x e') es)) 
		 
    | S.FunCall (S.FunId f, es) when is_binop f ->
       S.FunCall (S.FunId f, (List.map (fun y -> subst y x e') es))
		 
    | S.FunCall (S.FunId f, actuals) ->
       S.FunCall (S.FunId f, (List.map (fun y -> subst y x e') actuals))
    | S.UnknownFunCall (ef, actuals) ->       
       S.UnknownFunCall  ( (subst ef x e'), actuals )
			 
    | S.Switch (es, cases, default) ->
       S.Switch ( (subst  es x e'), cases, default)

  and analyse env = function

    (* literal *)
    | S.Literal l -> S.Literal l 

    (* varable *)
    | S.Variable (S.Id x) ->  S.Variable (S.Id x) 

    (* define *)
    | S.Define (S.Id x, e1, e2) ->
       let env' = bind x env in
       let x' = lookup x env' in

       let e1' = subst e1 x x' in
       let e2' = subst e2 x x' in
       
       S.Define (S.Id x', analyse env' e1',  analyse env' e2')

     | S.IfThenElse (c, t, f) ->
        S.IfThenElse ((analyse env c),  (analyse env t), (analyse env f) ) 

     | S.FunCall (S.FunId "allocate_block", es) ->
	S.FunCall (S.FunId "allocate_block", es)
		   
     | S.FunCall (S.FunId "read_block", es) ->
        S.FunCall (S.FunId "read_block",  (List.map (analyse env) es))
		  
     | S.FunCall (S.FunId "write_block", es) ->
        S.FunCall (S.FunId "write_block",  (List.map (analyse env) es)) 
		  
     | S.FunCall (S.FunId f, es) when is_binop f ->
	S.FunCall (S.FunId f, (List.map (analyse env) es) )
		  
     | S.FunCall (S.FunId f, actuals) ->
	S.FunCall (S.FunId f, (List.map (analyse env) actuals) )
	       
     | S.UnknownFunCall (ef, actuals) ->       
	 S.UnknownFunCall  ( (analyse env ef), actuals )
			   
     | S.Switch (e, cases, default) ->
	S.Switch ( (analyse env e), cases, default)

  in

  ldefinition [] p





let rec exit0 = function
  | [] -> []
  | [a] ->
     begin
       match a with 
       | T.DValue (T.Id x, (local,e)) ->
	  [T.DValue (T.Id x, (local,e@[labelled (T.Exit)])) ]
	  
       | T.DFunction(f,idl,block) ->
	  [T.DFunction  ( f, idl, block)]@
	    [T.DValue (fresh_variable (), ([],[labelled (T.Exit)])) ]
       | T.DExternalFunction (f) ->
          [T.DExternalFunction (f)]@
	    [T.DValue (fresh_variable (), ([],[labelled (T.Exit)])) ]
     end 
  | a::q -> a::(exit0 q)
     
    
(** [translate p env] turns the fopix program [p] into a semantically
    equivalent retrolix program. *)
let translate p env =
  
  let allocation_de_registre = false in
  let p = preprocess p in
  let p, env = translate' p env in
  let p =
    if allocation_de_registre then
      RetrolixRegisterAllocation.translate p
    else p
  in
  
  (exit0 p, env)


