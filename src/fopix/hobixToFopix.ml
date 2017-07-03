(** This module implements a compiler from Hobix to Fopix. *)

(** As in any module that implements {!Compilers.Compiler}, the source
    language and the target language must be specified. *)

module Source = Hobix
module S = Source.AST
module Target = Fopix
module T = Target.AST

(**

   The translation from Hobix to Fopix turns anonymous
   lambda-abstractions into toplevel functions and applications into
   function calls. In other words, it translates a high-level language
   (like OCaml) into a first order language (like C).

   To do so, we follow the closure conversion technique.

   The idea is a to make explicit the construction of closures, which
   represent functions as first-class objects. A closure is a block
   that contains a code pointer to a toplevel function [f] and all the
   values needed to execute the body of [f]. For instance, consider
   the following OCaml code:

   let f =
     let x = 6 * 7 in
     let z = x + 1 in
     fun y -> x + y * z

   The values needed to execute the function "fun y -> x + y * z" are
   its free variables "x" and "z". The same program with explicit usage
   of closure can be written like this:

   let g y env = env[1] + y * env[2]
   let f =
      let x = 6 * 7 in
      let z = x + 1 in
      [| g; x; z |]

   (in an imaginary OCaml in which arrays are untyped.)

   Once closures are explicited, there are no more anonymous functions!

   But, wait, how to we call such a function? Let us see that on an
   example:

   let f = ... (* As in the previous example *)
   let u = f 0

   The application "f 0" must be turned into an expression in which
   "f" is a closure and the call to "f" is replaced to a call to "g"
   with the proper arguments. The argument "y" of "g" is known from
   the application: it is "0". Now, where is "env"? Easy! It is the
   closure itself! We get:

   let g y env = env[1] + y * env[2]
   let f =
      let x = 6 * 7 in
      let z = x + 1 in
      [| g; x; z |]
   let u = f[0] 0 f

   (Remark: Did you notice that this form of "auto-application" is
   very similar to the way "this" is defined in object-oriented
   programming languages?)

*)

let error pos msg =
  Error.error "compilation" pos msg

let make_fresh_int =
  let r = ref 0 in
  fun () -> incr r; !r
  
let make_fresh_variable =
  let r = ref 0 in
  fun () -> incr r ; T.Id (Printf.sprintf "_%d" !r)

let make_fresh_variable' =
  let r = make_fresh_int () in
  fun () -> S.Id (Printf.sprintf "_%d" r)

let make_fresh_function_identifier =
  let r = ref 0 in
  fun () -> incr r; T.FunId (Printf.sprintf "_f%d" !r)

let define e f =
  let x = make_fresh_variable () in
  T.Define (x, e, f x)

let seq a b =
  define a (fun _ -> b)

let rec seqs = function
  | [] -> assert false
  | [x] -> x
  | x :: xs -> seq x (seqs xs)
       
let allocate_block e =
  T.(FunCall (FunId "allocate_block", [e]))

let write_block e i v =
  T.(FunCall (FunId "write_block", [e; i; v]))

let read_block e i =
  T.(FunCall (FunId "read_block", [e; i]))

let lint i =
  T.(Literal (LInt (Int32.of_int i)))

let identifier'' (T.Id x) = S.Id x

let rec write_var e i env = function
  | [] -> e, env
  | a :: tl ->
     let x = make_fresh_variable () in
     let o,new_env = write_var e (i+1) (Dict.insert (identifier'' x) (read_block e (lint i)) env) (tl) in
     T.Define (x, write_block e (lint i) a, o), env

let define_function id local corps =
  T.DefineFunction (id, local, corps)
  
let is_binary_primitive = function
  | "`+" | "`-" | "`*" | "`/" | "`<" | "`>" | "`<=" | "`>=" | "`=" -> true
  | _ -> false

let is_binary_app = function
  |S.Apply(e1,e2) ->
    begin
      match e1 with
      | S.Apply(e1',e2') ->
   begin
     match e1' with 
     |S.Variable (S.Id op) when is_binary_primitive op -> 
       true
     | _ -> false
   end
      | _ -> false
    end
  | _ -> assert false (** by case *) 

let free_variables =
  let module M = Set.Make (struct type t = S.identifier let compare = compare end) in
  let rec unions f = function
    | [] -> M.empty
    | [s] -> f s
    | s :: xs -> M.union (f s) (unions f xs)
  in
  let rec fvs = function
    | S.Literal l ->
      M.empty
    | S.Variable (S.Id x) when is_binary_primitive x ->
       M.empty
    | S.Variable x ->
       M.singleton x
    | S.Define (x, a, b) ->
      let sa = fvs a in
      let sb = fvs b in
      M.(union sa (remove x sb))
    | S.DefineRec (rdefs, a) ->
      assert false
    | S.ReadBlock (a, b) | S.Apply (a, b) ->
      unions fvs [a; b]
    | S.WriteBlock (a, b, c) | S.IfThenElse (a, b, c) ->
      unions fvs [a; b; c]
    | S.AllocateBlock a ->
      fvs a
    | S.Fun (x, e) ->
      M.remove x (fvs e)
    | S.Switch (a, b, c) ->
      let c = match c with None -> [] | Some c -> [c] in
      unions fvs (a :: Array.to_list b @ c)
  in
  fun e -> M.elements (fvs e)

(**

    A closure compilation environment relates an identifier to the way
    it is accessed in the compiled version of the function's
    body.

    Indeed, consider the following example. Imagine that the following
    function is to be compiled:

    fun x -> x + y

    In that case, the closure compilation environment will contain:

    x -> x
    y -> "the code that extract the value of y from the closure environment"

    Indeed, "x" is a local variable that can be accessed directly in
    the compiled version of this function's body whereas "y" is a free
    variable whose value must be retrieved from the closure's
    environment.

*)
let extenv = ref []
let lookup elt =
    List.mem elt !extenv

type environment =
    (HobixAST.identifier, FopixAST.expression) Dict.t

let initial_environment () =
  Dict.empty


    
(** [translate p env] turns an Hobix program [p] into a Fopix program
    using [env] to retrieve contextual information. *)
let translate (p : S.t) env =
  let rec program env defs =
    List.(flatten (map definition defs)), env
  and definition = function
    | S.DeclareExtern id ->
       extenv := id :: (!extenv);
      [T.ExternalFunction (function_identifier id)]
    | S.DefineValue (x, e) ->
      let fs, e = expression Dict.empty e in
      fs @ [T.DefineValue (identifier x, e)]
    | S.DefineRecValue rdefs ->
       define_recursive_functions rdefs

  and define_recursive_functions rdefs =
    let ptrl = List.map (fun (x,_) -> (x, make_fresh_variable ())) rdefs in
    let env = List.fold_left (fun a (x,y) -> Dict.insert x (T.Variable y) a) Dict.empty ptrl in
    let ll =
      List.map2 (fun (x,y) x' -> define_recursive_functions' y env x') ptrl rdefs
    in

    let r1 = List.map (fun (x,_) -> x) ll |> List.flatten in
    let r2 = List.map (fun (_,y) -> y) ll in
    r2 @ r1
	   
  and define_recursive_functions' ptr env ffun = 
    let (fx, e) = ffun in
    match e with
    | S.Fun (x', e') as f ->
       let id_fun = make_fresh_function_identifier () in
       let fvs = free_variables f in
       let alloc = T.DefineValue (ptr, allocate_block ((List.length fvs)+1 |> lint)) in
       let clos,ptr, env = closure' ptr (T.Literal (T.LFun id_fun)) fvs env in
       let l, e'' = expression env e' in
       let dfun = T.DefineFunction (id_fun, [ identifier x' ; ptr ], e'') in
       let tclos = definevalue_of_define clos in
       l @ [ dfun ] @ tclos @ [ T.DefineValue (identifier fx, T.Variable ptr) ], alloc
	     

    | _ -> assert false

  and definevalue_of_define = function
    | T.Define (x, e1, e2) ->
       T.DefineValue (x, e1) :: definevalue_of_define e2
    | _ -> []
	 
  and expression env = function
    | S.Literal l ->
       [], T.Literal (literal l)
		     
    | S.Variable x ->
       [], (match Dict.lookup x env with
	    | None -> T.Variable (identifier x)
	    | Some (T.FunCall (T.FunId "allocate_block", vs))->
	       T.Variable (identifier x)
	    |  Some s -> s)
	
    | S.Define (x, a, b) ->
       let (l1, a') = expression env a in
       let (l2, b') = expression (Dict.insert x a' env) b in
       l1 @ l2, T.Define (identifier x, a', b')
			 
    | S.DefineRec (rdefs, a) ->
       
       let aux ptr env def =
	 let (fx, e) = def in
	 (match e with
	  | S.Fun (x', e') as f ->
	     let id_fun = make_fresh_function_identifier () in
	     let fvs = free_variables f in
	     let alloc = fun x ->
	       T.Define (ptr, allocate_block ((List.length fvs)+1 |> lint), x) in
	     let clos,ptr, env = closure' ptr (T.Literal (T.LFun id_fun)) fvs env in
	     let l, e'' = expression env e' in
	     let dfun = T.DefineFunction (id_fun, [ identifier x' ; ptr ], e'') in
	     
	     l @ [ dfun ], (fun x -> T.Define (identifier fx, clos, x)), alloc
									   
	     | _ -> assert false)
	   
       in

       let ptrl =
	 List.map (fun (x,y) -> (x, make_fresh_variable ())) rdefs
       in
       let env =
	 List.fold_left (fun a (x,y) ->
			 Dict.insert x (T.Variable y) a) Dict.empty ptrl
       in  
       let ll = List.map2 (fun (_,y) x -> aux y env x) ptrl rdefs in
       let lalloc = List.map (fun (x,y,z) -> z) ll in
       let lffun = List.map (fun (x,y,z) -> y) ll in
       let ldefs = List.map (fun (x,y,z) -> x) ll |> List.flatten in

       let l',a' = expression env a in
       let lll = List.fold_left (fun a x -> x a) a' lffun in
       let lll' = List.fold_left (fun a x -> x a) lll lalloc in
       l'@ldefs, lll'

    | S.Apply (a, b) as e when is_binary_app e ->
	 let l2, a2 = expression env b in
	 (match a with
	 | S.Apply (a',b') ->
	    let l1, a1 = expression env b' in
	    begin
	      match a' with 
	      |S.Variable (S.Id op)->
		l1 @ l2,T.FunCall (T.FunId op, [a1;a2] ) 
	      | _ -> assert false
	    end
	 | _ -> assert false)
	 
    | S.Apply (a, b) ->
       
       (match expression env a with
	| l1,T.Variable (T.Id x) when lookup (S.Id x) ->
	   let l2,b' = expression env b in
	   l1@l2, T.FunCall (T.FunId  (x), [ b' ;T.Variable (T.Id x) ])
	| l1,T.Variable _ as var ->
	   let l2,b' = expression env b in
	  l1@l2, T.UnknownFunCall (read_block (snd var) (lint 0), [ b' ; (snd var) ])

       | l1,a' ->
	  let l2, b' = expression env b in
	  let ufuncall = fun x ->
	    T.UnknownFunCall (read_block (T.Variable x) (lint 0), [ b' ; T.Variable x ])
	  in
	  l1@l2, define a' ufuncall)
	 
		       	    
    | S.IfThenElse (a, b, c) ->
       let afs, a = expression env a in
       let bfs, b = expression env b in
       let cfs, c = expression env c in
       afs @ bfs @ cfs, T.IfThenElse (a, b, c)

    | S.Fun (x, e) as f ->

       let id_fun = make_fresh_function_identifier () in
       let fvs = free_variables f in
       let clos,ptr, env =
	 closure (make_fresh_variable ()) (T.Literal (T.LFun id_fun)) fvs env
       in
       let l, e' = expression env e in
       let dfun = T.DefineFunction (id_fun, [ identifier x ; ptr ], e') in
       l @ [ dfun ], clos

    | S.AllocateBlock a ->
      let afs, a = expression env a in
      (afs, allocate_block a)
	
    | S.WriteBlock (a, b, c) ->
      let afs, a = expression env a in
      let bfs, b = expression env b in
      let cfs, c = expression env c in
      afs @ bfs @ cfs,
      T.FunCall (T.FunId "write_block", [a; b; c])
		
    | S.ReadBlock (a, b) ->
      let afs, a = expression env a in
      let bfs, b = expression env b in
      afs @ bfs,
      T.FunCall (T.FunId "read_block", [a; b])
		
    | S.Switch (a, bs, default) ->
      let afs, a = expression env a in
      let bsfs, bs = List.(split (map (expression env) (Array.to_list bs))) in
      let dfs, default = match default with
  | None -> [], None
  | Some e -> let bs, e = expression env e in bs, Some e
      in
      afs @ List.flatten bsfs @ dfs,
      T.Switch (a, Array.of_list bs, default)

  and literal = function
    | S.LInt x -> T.LInt x
    | S.LString s -> T.LString s
    | S.LChar c -> T.LChar c
    | S.LBool b -> T.LBool b

  and identifier (S.Id x) = T.Id x

  and function_identifier (S.Id x) = T.FunId x

  and closure ptr f fvs env =

    let fvs' = fvs |> List.map (fun x -> snd (expression env (S.Variable x))) in
    let fvs'' = fvs |> List.map (fun x -> T.Variable (identifier x)) in
    (* pointeur de la zone memoire *)
    let mem = ptr in
    
    (* allocation de la memoire *)
    let alloc = allocate_block (fvs |> List.length |> (+) 1 |> lint) in
    
    (* on ecrit chaque variable dans le block *)
    let pos = ref 0 in
    let write_fvs = List.map (fun x -> incr pos ; write_block (T.Variable mem) (lint !pos)
							      x) fvs' in
    let pos = ref 0 in
    let read_fvs = List.map (fun x -> incr pos ; read_block (T.Variable mem) (lint !pos)) fvs in
    let env = List.fold_left2 (fun a x y ->
			       match x with
			       | T.Variable (T.Id x') ->
				  Dict.insert (S.Id x') y a
			       | _ -> a) env fvs'' read_fvs in
    
    (* on definit une suite de definition avec comme valeur de retour mem *)
    let seq = List.fold_left (fun a x -> T.Define (make_fresh_variable (), x, a)) (T.Variable mem) write_fvs in
    
    T.Define (mem, alloc, T.Define (make_fresh_variable (), write_block (T.Variable mem) (lint 0) f, seq)), mem, env
														   
  and closure' ptr f fvs env =
    
    let fvs' = fvs |> List.map (fun x -> snd (expression env (S.Variable x))) in
    let fvs'' = fvs |> List.map (fun x -> T.Variable (identifier x)) in
    (* pointeur de la zone memoire *)
    let mem = ptr in

  

    (* on ecrit chaque variable dans le block *)
    let pos = ref 0 in
    let write_fvs = List.map (fun x -> incr pos ; write_block (T.Variable mem) (lint !pos)
							      x) fvs' in
    let pos = ref 0 in
    let read_fvs = List.map (fun x -> incr pos ; read_block (T.Variable mem) (lint !pos)) fvs in
    let env = List.fold_left2 (fun a x y ->
			       match x with
			       | T.Variable (T.Id x') ->
				Dict.insert (S.Id x') y a
			       | _ -> a) env fvs'' read_fvs in
    
    (* on definit une suite de definition avec comme valeur de retour mem *)
    let seq = List.fold_left (fun a x -> T.Define (make_fresh_variable (), x, a)) (T.Variable mem) write_fvs in
    
    T.Define (make_fresh_variable (), write_block (T.Variable mem) (lint 0) f, seq), mem, env
											    
  in
  program env p
