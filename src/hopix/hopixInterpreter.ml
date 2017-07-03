open Position
open Error
open HopixAST

       
(** [error pos msg] reports runtime error messages. *)
let error positions msg =
  errorN "execution" positions msg

(** Every expression of hopix evaluates into a [value]. *)
type 'e gvalue =
  | VString         of string
  | VChar           of char
  | VUnit
  | VBool           of bool
  | VTaggedValues   of constructor * 'e gvalue list
  | VInt            of Int32.t
  | VAddress        of Memory.address
  | VPrimitive      of string * ( 'e gvalue -> 'e gvalue)
  | VFun            of pattern located * expression located * 'e

type ('a, 'e) coercion = 'e gvalue -> 'a option

(* recupere le int d'un value *)
let value_as_int      = function VInt x -> Some x | _ -> None
let value_as_bool     = function VBool x -> Some x | _ -> None
let value_as_char     = function VChar c -> Some c | _ -> None

type ('a, 'e) wrapper = 'a -> 'e gvalue

         
(* creer un vint *)
let int_as_value x  = VInt x


(* recupere le string d'un ast *)
let string_of_id = function Id x -> x

              
(* recupere le string d'une variable *)
let rec string_of_Patt =function
  | PVariable t -> 
     let (Id x) = Position.value t in x
  | PTaggedValue (k,[]) -> let (KId k') = (Position.value k) in k'
  | PTaggedValue (k,l) ->

     let rec aux = function
       | [] -> assert false
       | [a] -> string_of_Patt' a
       | a::b -> (string_of_Patt' a)^", "^ aux b
     in (let (KId k') = (Position.value k) in k')^"("^ aux l ^")"

      
  | _ -> assert false 

and string_of_Patt' x = string_of_Patt (Position.value x)  


(**

fonction modifier ancien protype : 
let primitive name ?(error = fun () -> assert false) coercion wrapper f

**)

let primitive name  coercion wrapper f =
  VPrimitive (name, 
  fun x ->
    match coercion x with
      | None -> (assert false)
      | Some x -> wrapper (f x)
  )

let print_value m v =
  let max_depth = 5 in
  let rec print_value m d v =
    if d >= max_depth then "..." else
      match v with 
        | VString x -> "\""^ x ^"\""
        | VUnit  -> "()"
        | VBool x ->
          string_of_bool x
        | VInt x ->
          Int32.to_string x
        | VPrimitive (s, _) -> 
          Printf.sprintf "<primitive: %s>" s
        | VFun (x, _ , _ ) -> 
         "<fun>" 
        | VAddress x -> 
          print_record_value m d (Memory.read_block m x) 
        | VTaggedValues (sym,[]) -> 
          begin
          match sym with 
            | KId x -> x
          end
        | VTaggedValues (KId sym, largs) -> 
          let rec aux = function
           | [] -> ""
           | [a] -> print_value m (d+1) a
           | h :: tl -> print_value m (d+1) h ^ ", " ^ aux tl 
         in
          sym^"("^ aux largs ^")"

        | VChar x -> 
          "\'"^Char.escaped x ^"\'"

  and print_record_value m d r =
    "{ " ^ String.concat "; " (List.map (print_field m d) r) ^ " }"
  and print_field m d (LId l, v) =
    l ^ " = " ^ print_value m (d + 1) v

in
  print_value m 0 v
(* environnement *)

module Environment : sig
  type t
  val empty : t
  val bind    : t -> identifier -> t gvalue -> t
  val extracvf : t -> (identifier * t gvalue) list -> (identifier * t gvalue)  list
  val compose : t -> t -> t
  val update  : Position.t -> identifier -> t -> t gvalue -> unit
  exception UnboundIdentifier of identifier * Position.t
  val lookup  : Position.t -> identifier -> t -> t gvalue
  val last    : t -> (identifier * t gvalue * t) option
  val print   : t gvalue Memory.t -> t -> string
end = struct

  type t =
    | EEmpty
    | EBind of identifier * t gvalue ref * t

  let empty = EEmpty

  let bind e x v =
    EBind (x, ref v, e)


  exception UnboundIdentifier of identifier * Position.t

  let lookup' pos x =
    let rec aux = function
      | EEmpty -> raise (UnboundIdentifier (x, pos))
      | EBind (y, v, e) ->
        if x = y then v else aux e
    in
    aux


  let rec compose env1 env2 =
    match env1 with 
      | EBind (x1, v, EEmpty) -> 
        EBind (x1, v, env2)
      | EBind (x1, v, o) ->
        EBind (x1, v, compose o env2)
      | EEmpty -> env2


  let lookup pos x e = !(lookup' pos x e)

  let update pos x e v =
    lookup' pos x e := v

  let last = function
    | EBind (x, v, e) -> Some (x, !v, e)
    | EEmpty  -> None

  let rec extracvf env acc = 
   match last env with
    | None -> acc
    | Some (a,b,c) -> 
     begin 
     match b with  
     | VFun (x,exp,env) -> 
      extracvf c ((a, (VFun (x,exp,env)) )::acc)
      | _ -> extracvf c acc
     end

  let print_binding m (Id x, v) =
    x ^ " = " ^ print_value m !v

  let print m e =
    let b = Buffer.create 13 in
    let push x v = Buffer.add_string b (print_binding m (x, v)) in
    let rec aux = function
      | EEmpty -> Buffer.contents b
      | EBind (x, v, EEmpty) -> push x v; aux EEmpty
      | EBind (x, v, e) -> push x v; Buffer.add_string b "\n"; aux e
    in
    aux e
  end

  
type value = Environment.t gvalue

type formals = identifier list

type runtime = {
  memory      : value Memory.t;
  environment : Environment.t;
}


type observable = {
  new_memory      : value Memory.t;
  new_environment : Environment.t; 
}

(** [primitives] is an environment that contains the implementation
    of all primitives (+, <, ...). *)
let primitives =
  let intbin name out op =
    VPrimitive (name, function VInt x ->
      VPrimitive (name, function
        | VInt y -> out (op x y)
        | _ -> assert false (* By typing. *)
      )
      | _ -> assert false (* By typing. *)
    )
  in
  let boolbin name out op =
    VPrimitive (name, function VBool x ->
      VPrimitive (name, function
        | VBool y -> out (op x y)
        | _ -> assert false (* By typing. *)
      )
      | _ -> assert false (* By typing. *)
    )
  in
  let bind_all what l x =
    List.fold_left (fun env (x, v) -> Environment.bind env (Id x) (what x v)) x l
  in

  (* Define arithmetic binary operators. *)
  let binarcomp name =
    intbin name (fun x -> VBool x) in
  let binarcompops = 
    [ ("`<", (<)); ("`>", (>)); ("`=", (=)); ("`<=", (<=));("`>=", (>=) )] in
  let binarith name =
    intbin name (fun x -> VInt x) in
  let binarithops = Int32.(
    [ ("`+", add); ("`-", sub); ("`*", mul); ("`/", div) ]
  )in
  let binarlo name =
    boolbin name (fun x -> VBool x) in
  let logique = 
    [ ("`&&", (&&)); ("`||", (||)) ] in
  Environment.empty
  |> bind_all binarith binarithops 
  |> bind_all binarcomp binarcompops 
  |> bind_all binarlo logique 

let initial_runtime () = {
  environment = primitives;
  memory = Memory.fresh ()
}


(* let memory = Memory.init *)

         
let rec evaluate runtime ast =

  try
    let runtime' = List.fold_left definition runtime ast in
    (runtime', extract_observable runtime runtime')
  with Environment.UnboundIdentifier (Id x, pos) ->
    Error.error "interpretation" pos (Printf.sprintf "`%s' is unbound." x)


(* evalue une definition *)
and definition runtime d =
  match Position.value d with
   | DefineRecValue l -> 
    let v,memory = definitionRec runtime.environment runtime.memory l in
     {
        environment = v;
        memory
      }
   | DefineValue (x, e) -> 
   let v, memory = expression' runtime.environment runtime.memory e in
   {
    environment = bind_identifier runtime.environment x v;
    memory
   }
   | _ -> runtime

and definitionRec environment memory = function
  | [] -> environment,memory
  | (a,b)::l -> 
    let evalb,memory = (expression' environment memory b) in
    let environment = bind_identifier environment a evalb in
    definitionRec environment memory l

(* [definition pos runtime d] evaluates the new definition [d]
   into a new runtime [runtime']. In the specification, this
   is the judgment:

      E, M ⊢ dᵥ ⇒ E', M'

*)

and expression' environment memory e =
  expression (position e) environment memory (value e)

(* [expression pos runtime e] evaluates into a value [v] if *)
(*
and 
  E = [runtime.environment], M = [runtime.memory]
*)
and expression position environment memory = function  
  | Fun (x, e) -> VFun (x, e, environment) , memory
  | IfThenElse (b,e1,e2) ->
       let v, memory = expression' environment memory b in 
    begin match value_as_bool v with
      | None -> assert false (* By typing. *)
      | Some true -> expression' environment memory e1
      | Some false -> expression' environment memory e2
    end

  | Apply (a, b) ->
     
    let vb, memory =  expression' environment memory b in 
    begin match expression' environment memory a with
      | VPrimitive (_, f), memo  -> f vb, memo
      | VFun (patt, exp, env), memo ->
        let lvf = 
          Environment.extracvf environment [] in
        let concatRun = 
         let rec bind_vf envf lvf = 
           match lvf with
           | [] -> envf
           | (a,b)::q -> bind_vf (Environment.bind envf a b) q in 
          bind_vf env lvf in 
        let environmentSet = unify (value patt) vb concatRun memory in
          expression' environmentSet memory exp

      | k, memo -> 
        assert false (* By typing. *)
    end
  | Literal l ->
     literal (Position.value l), memory

  (* cas variable : recupere la valeur associé de la variable *)
  | Variable x -> 
     Environment.lookup (Position.position x) (Position.value x) environment,memory

  (* definition *)
  | Define (x, ex, e) -> 
    let v,memory = expression' environment memory ex in
    let environmentSet = bind_identifier environment x v in 
    expression' environmentSet memory e


  | DefineRec (l, e) -> 

    let corps,memory = (definitionRec environment memory l) in 
        expression' corps memory e

  | Tagged (contruct, taglist) -> 
    contructor_type environment memory taglist (Position.value contruct)

  | Case (e, bl) ->
     let ee,memo = expression' environment memory e in
     
     let rec aux = function
       | [] -> failwith "Mismatch failure"
       | br :: tl ->
    try branch' environment ee memory br
    with _ -> aux tl
     in
     aux bl
       
  | TypeAnnotation(e,_) -> expression' environment memory e

  | Record (l) -> 
    let subMem = createRec environment memory [] l in
    let addr,newmem = Memory.allocate memory subMem in 
      VAddress(addr),newmem

  | Field (exp, lab ) -> 
    let addr,memo = expression' environment memory exp in 
      begin
        match addr with
          | VAddress add -> 
             Memory.read memo add (Position.value lab),memo
          | _ -> addr,memo 
      end
  | ChangeField (e1, lab , e2) -> 
    let addr,memo = expression' environment memory e1 in 
      begin
        match addr with
          | VAddress add -> 
           let exp2,memoy = expression' environment memo e2 in
            VUnit,(Memory.write memoy add (Position.value lab) exp2)
          | _ -> failwith "index syntaxe 1"
      end


and setList newVal acc = function
  | [] -> (List.rev acc)
  | (x,y)::q when  (fst newVal) = x -> setList newVal (newVal::acc) q
  | (x,y)::q -> setList newVal ((x,y)::acc) q

and createRec environment memory acc = function
  | [] -> (List.rev acc)
  | (a,b)::q->  
    let valeur,memo = expression' environment memory b in
    let couple = ( (Position.value a) , valeur ) in 
      createRec environment memo (couple::acc) q

and pattern' id =
  pattern (value id)

and pattern = function
  | PVariable x ->  x
  | _ -> failwith "salut"

and unify patt expr environment memory = match patt, expr with

  | PTypeAnnotation (p,_),_ -> unify (value p) expr environment memory
  | PVariable x,_ ->  bind_identifier environment x expr
  | PLiteral l,_ ->
     begin
       match value l, expr with
       | LString s, VString s' when s = s' -> environment
       | LChar c, VChar c' when c = c' -> environment
       | LInt i, VInt i' when i = i' -> environment
       | LBool b, VBool b' when b = b' -> environment
       | _ -> failwith "error unification"
     end
  | PTaggedValue (sym, largs), VTaggedValues (KId sym', largs')
       when let (KId id) = value sym in id = sym' ->
     List.fold_left2 (fun a x y -> unify (value x) y a memory) environment largs largs'
  
  | PRecord largs, VAddress addr ->
     begin
       match (Memory.read_block memory addr) with
       | largs' ->

    let get_str x = let (s) = value x in s in
    let new_largs = List.map (fun (x,y) -> (get_str x, y)) largs in
    let lu = List.map (fun (x,y) -> (value y, List.assoc x largs') ) new_largs in
    List.fold_left (fun a (x, y) -> unify x y a memory) environment lu
     end

       
  | POr largs,_ ->

     let rec aux env e = function
       | [] -> failwith "error unification"
       | h::tl ->
    begin
      try
        unify (value h) e environment memory
      with _ -> aux env e tl
    end
     in aux environment expr largs

  | PAnd largs, _ ->

     let rec aux env e = function
       | [] -> env
       | h::tl ->
    (try
              let new_env = unify (value h) e env memory in
              aux new_env e tl
      with _ -> failwith "error unification")
     in aux environment expr largs
           
  | PWildcard,_ -> environment
  | _ -> failwith "error unification"

    
and branch' environment ee memory br =
  branch environment ee memory (value br)
   
and branch environment ee memory br =
  let (Branch (patt, expr)) = br in
  try
    let environment' = unify (value patt) ee environment memory in
    expression' environment' memory expr
  with _ -> failwith "error" 
  
and updateRuntime env mem=
  {environment = env ; memory = mem} 

and bind_identifier environment x v =
  Environment.bind environment (Position.value x) v

and contructor_type environment memory valuelist = function
  | KId x ->     
    let rec contructor environment memory acc = function
      |  [] -> VTaggedValues (KId x, List.rev acc),memory
      |  a::q -> 
        let valeur,memo = expression' environment memory a in 
          contructor environment memo (valeur::acc) q
    in contructor environment memory [] valuelist

and literal = function
  | LString x -> VString x
  | LChar x -> VChar x
  | LBool x -> VBool x
  | LInt x ->  VInt x
 
and extract_observable runtime runtime' =
  let rec substract new_environment env env' =
    if env == env' then new_environment
    else
      match Environment.last env' with
        | None -> assert false (* Absurd. *)
        | Some (x, v, env') ->
          let new_environment = Environment.bind new_environment x v in
          substract new_environment env env'
  in
  {
    new_environment =
      substract Environment.empty runtime.environment runtime'.environment;
    new_memory =
      runtime'.memory
  }

let print_observable runtime observation =
  Environment.print observation.new_memory observation.new_environment
