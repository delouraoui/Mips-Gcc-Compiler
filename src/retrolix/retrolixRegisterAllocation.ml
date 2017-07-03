(**

   The register allocation translates a Retrolix program into an
   equivalent Retrolix program that uses hardware registers as much as
   possible to hold intermediate results.

   Register allocation is done in two steps:

   - a static analysis called "Liveness Analysis of Variables" is
   performed to compute a graph. It approximates the interference
   relation of program variables, i.e. the intersection between the
   live ranges of variables. The nodes of the graph are the program
   variables and, in this graph, a node for 'x' and a node 'y' are
   connected iff 'x' and 'y' are in interference.

   - a graph coloring algorithm is executed on the interference graph:
   if two variables live at the same time, then their values cannot
   be carried by the same register ; thus, it suffices to use a different
   color for their nodes. Graph coloring is NP-complete. Yet, we will
   use a simple recursive algorithm that provides good results in
   practice.

*)

open RetrolixAST

module LabelMap = Map.Make (struct
  type t = label
  let compare = compare
end)

(** Liveness Analysis. *)
type location = lvalue

module LSet = Set.Make (struct
    type t = location
    let compare = compare
end)

type liveness_analysis_result = {
  live_in  : LSet.t LabelMap.t;
  live_out : LSet.t LabelMap.t;
  }


(** renvoie le string  *)
let string_of_lvalue = function
  | `Variable (Id v) -> v
  | `Register (RId r) -> r
			   
let string_of_label l = let (Label s) = l in s
let string_of_llabel ll = match ll with
  | [] -> "()"
  | _ ->
     "( " ^
       (List.fold_left (fun a l -> a ^ string_of_label l) "" ll) ^
	 " )"

let string_of_live live =
  let ll = 
    LabelMap.bindings live
  in
  let lll =
    List.map (fun (x, ls) -> (x, LSet.elements ls)) ll
  in
  let ff =
    fun l -> List.map string_of_lvalue l
  in
    
  let l' =
    List.map (fun (x, ls) ->
	      "(" ^ string_of_label x ^ ", " ^
		List.fold_left
		  (fun a x -> a ^ " " ^ x) "" (ff ls) ^ ")") lll
  in
  List.iter print_endline l'
  
		      
let find_default d k m =
  try LabelMap.find k m with Not_found -> d

let empty_results =
  {
    live_in = LabelMap.empty;
    live_out = LabelMap.empty;
  }

let lvalue_of_rvalue = function
  | `Immediate l -> None
  | (`Variable _ | `Register _) as lv -> Some lv


let add_lvalue set rv = match lvalue_of_rvalue rv with
  | None -> set
  | Some s -> LSet.add s set
    
(** soit [i] une instruction *)
    
(** [def i] ensemble des temporaires ecrits par [i]. *)
let def i = match i with
  | Call (lv,_,_) -> LSet.add lv LSet.empty
  | Assign (lv,_,_) -> LSet.add lv LSet.empty
  | _ -> LSet.empty

(** [use i] ensemble des temporaires lus par [i]. *)
let use i = match i with
  | (Call (_,rv, rvl) | TailCall (rv, rvl)) ->
     let set = add_lvalue LSet.empty rv in
     List.fold_left (fun a x -> add_lvalue a x) set rvl
  | (Ret rv | Switch (rv,_,_)) -> add_lvalue LSet.empty rv 
  | (Assign (_,_,rvl) | ConditionalJump (_,rvl,_,_)) ->
     List.fold_left (fun a x -> add_lvalue a x) LSet.empty rvl
  | _ -> LSet.empty

let rec successors = function
  | DValue (_, b) :: _ ->
     let s= successors_block b in
     fun l -> List.assoc l s

  | _ -> assert false

and successors_block b =
  let local, li = b in
  successors_li li
					    
and successors_li = function
  | [] -> []
  | [ (l,i) ] ->
     (match successors_instr i with
      | None -> [ (l, []) ]
      | Some s -> [ (l, s) ])
  | (l1,i1) :: (l2,i2) :: tl ->
     (match successors_instr i1 with
      | None -> (l1, [l2]) :: successors_li ( (l2,i2) :: tl )
      | Some s -> (l1, s) :: successors_li ( (l2,i2) :: tl ))
       
and successors_instr = function
  | Jump l' -> Some [l']
  | ConditionalJump (b,rvl,lt,lf) -> Some [lt;lf]
  | Switch (rv,al,None) -> Some (Array.to_list al)
  | Switch (rv,al,Some ld) -> Some (Array.to_list al @ [ld]) 
  | _ -> None

let union_lset lset =
  List.fold_left (fun a x -> LSet.union a x) LSet.empty lset

let equal a a' b b' =
  let la,la' =
    Array.to_list a,
    Array.to_list a'
  in
  let lb,lb' =
    Array.to_list b,
    Array.to_list b'
  in
  la = la' && lb = lb'

let rec eequal a a' b b' n =
  eequal' a a' b b' 0 n
  
and eequal' a a' b b' pos n =
  if pos = n then true
  else if a.(pos) = a'.(pos) && b.(pos) = b'.(pos) then
    eequal' a a' b b' (pos+1) n
  else false

let map_of_array liveness n tlabel array =
  let map = ref liveness in
  for i=0 to (n-1) do
    map := LabelMap.add (tlabel.(i)) array.(i) !map
  done; !map
	  
let compute_analysis' liveness n tlabel tinstr tsucc =
  
  let lin,lin'=
    Array.make n LSet.empty,
    Array.make n LSet.empty
  in
  let lout,lout'=
    Array.make n LSet.empty,
    Array.make n LSet.empty
  in
  let bool = ref false in

  while not (!bool) do
    
    (** one vivacity *)
    for i=0 to (n-1) do
    
      lin' .(i) <- lin .(i);
      lout' .(i) <- lout .(i);
      lin .(i) <-
	LSet.union (use (tinstr.(i)))
		   (LSet.diff (lout.(i)) (def (tinstr.(i))));
      lout .(i) <-
	List.fold_left (fun a x -> LSet.union a (lin.(x)))
		       LSet.empty tsucc.(i);
      
    done;
    (** *)

    bool := eequal lin lin' lout lout' n;
      
  done;
  map_of_array liveness.live_in n tlabel lin,
  map_of_array liveness.live_out n tlabel lout

	       
let liveness_analysis'' liveness li =
  let succ = successors_li li in
  let tlabel =
    Array.of_list (List.map (fun (l,_) -> l) li)
  in
  let tinstr =
    Array.of_list (List.map (fun (_,i) -> i) li)
  in
  let pos = ref (-1) in
  let aa' =
    List.map (fun (l,_) -> incr pos ; (l, !pos)) li
  in
  let isucc =
    List.map (fun (s, ls) ->
	      List.assoc s aa', List.map (fun x -> List.assoc x aa') ls)
	     succ
  in
  let tsucc =
    Array.of_list (List.map (fun (_, li) -> li) isucc)
  in
  let n = List.length li in
  let lin,lout= compute_analysis' liveness n tlabel tinstr tsucc in
  {live_in=lin;live_out=lout}
     
  
	       
(** [liveness_analysis p] returns the liveness analysis of [p]. *)

let rec fin succ s =
  LSet.union (use s) (LSet.diff (fout succ s) (def s))
and fout succ s =
  List.fold_left (fun a x -> LSet.union a (fin succ x)) LSet.empty (succ s) 
	     
let rec liveness_analysis' liveness = function

  | [] -> liveness
    
  | DValue (_, b) :: tl ->
     let local, li = b in
     liveness_analysis' (liveness_analysis'' liveness li) tl
     
  | DFunction (fun_id, id_l, b) :: tl ->
     let local, li = b in
     liveness_analysis' (liveness_analysis'' liveness li) tl

  | _ :: tl -> liveness_analysis' liveness tl

let liveness_analysis p =
  liveness_analysis' {live_in=LabelMap.empty;live_out=LabelMap.empty} p

		
(** Interference graph. *)

(** In the interference graph, there will be two kinds of edges: *)
type relation =
  (** If two variables cannot be represented in the same register
      because their liveness ranges intersect, we say that they are in
      a conflict relation. *)
  | Conflict

  (** If two variables are related by a MOVE instruction, we will try
      to put them in the same register, we say that they are in
      a preference relation. *)
  | Preference

(** The node of the interference graph are lvalues and its edges are
    labelled by [relation]. *)
module IGraphColoring = GraphColoring.Make
  (struct
    type t = relation
    let compare = compare
    let all = [ Conflict; Preference ]
    let preference = Preference
    let conflict = Conflict
    let to_string = function
      | Conflict -> "<>"
      | Preference -> "="
   end)
  (struct
    type t = lvalue
    let compare = compare
    let to_string : t -> string = function
      | `Register (RId r) -> "$" ^ r
      | `Variable (Id r) -> r
   end)
  (struct
    type t = register
    (** The following will change when we will seriously implement the MIPS backend.  *)
    let all = MipsArch.(List.map (fun r -> RId (string_of_register' r)) all_registers)
    let cardinal = List.length all
    let to_string (RId r) = r
   end)

module IGraph = IGraphColoring.Graph

type interference_graph = IGraph.t

(**

   To construct the interference graph:

   1. At any non-move instruction that defines variable a (where
   live-out variables are b1, ..., bj) add interference edges (a, b1),
   ..., (a, bj).

   2. At a move instruction a ← c (where variables b1, ..., bj are
   live-out) add interference edges (a, b1), ..., (a, bj) for any bi
   that is not the same as c.

 *)

(** retournes lensemble des variables du block *)
let set_of_node b =
  List.fold_left (fun a (l,i) ->
		  let a'=
		    try LSet.union (def i) a with _ -> a
		  in
		  let a'' =
		    try LSet.union (use i) a' with _ -> a'
		  in a'') LSet.empty b

let rec set_of_node' set = function
  | (DValue (_, (_, li)) :: tl | DFunction (_,_,(_,li)) :: tl) ->
     let set =
       set_of_node_lintr set li
     in
     set_of_node' set tl

  | _ :: tl -> set_of_node' set tl

  | [] -> set

and set_of_node_lintr set = function
  | [] -> set
  | (l,i) :: tl ->
     let set = LSet.union set (def i) in
     let set = LSet.union set (use i) in
     set_of_node_lintr set tl

     
let igraph_of_setnode g set =
  List.fold_left
    (fun a x -> try IGraph.add_node a [ x ] with _ -> a) g (LSet.elements set)

let color = ref (IGraph.empty)

let edge_of_instr x liveness =
  let (l, i) = x in
  match i with

  (* move instruction *)
  | Assign (t, Load, [ `Register r ]) ->
     (find_default LSet.empty l liveness.live_out
      |> LSet.elements
      |> List.map (fun x -> (t,Conflict,x))
      |> List.filter (fun (a,_,b) -> a <> b)
      |> List.filter (fun (a,_,b) -> b <> `Register r))
  (* @ [ (t,Preference,`Register r) ] *)
		    
  | Assign (t, Load, [ `Variable v ]) ->
     (find_default LSet.empty l liveness.live_out
      |> LSet.elements
      |> List.map (fun x -> (t,Conflict,x))
      |> List.filter (fun (a,_,b) -> a <> b)
      |> List.filter (fun (a,_,b) -> b <> `Variable v))
     (* @ [ (t,Preference,`Variable v) ] *)

  (* non-move instruction *)
  | (Call (t, _, _) | Assign (t, _, _)) ->
     find_default LSet.empty l liveness.live_out
     |> LSet.elements
     |> List.map (fun x -> (t,Conflict,x))
     |> List.filter (fun (a,_,b) -> a <> b)

  (* not def instruction *)
  | _ -> []
  
     
let add_edge g n1 e n2 =
  let g = IGraph.add_node g [n1] in
  let g = IGraph.add_node g [n2] in
  IGraph.add_edge g n1 e n2
			    
let interference_graph'' g b liveness : interference_graph =
  (* let new_g = igraph_of_setnode g (set_of_node b) in *)
  let ledge =
    List.map (fun x -> edge_of_instr x liveness) b
    |> List.flatten
  in
  List.fold_left (fun a (x,r,y) -> IGraph.add_edge a x r y) g ledge

let rec interference_graph' g p liveness =
  match p with
  | [] -> g
	    
  | DValue (_, block) :: tl ->
     let (local, li) = block in
     let new_g =
       interference_graph'' g li liveness
     in
     interference_graph' new_g tl liveness
     
  | DFunction (_,_, block) :: tl ->
     let (local, li) = block in
     let new_g =
       interference_graph'' g li liveness
     in
     interference_graph' new_g tl liveness
     
  | _ :: tl -> interference_graph' g tl liveness

let interference_graph p liveness =
  let g = igraph_of_setnode IGraph.empty (set_of_node' LSet.empty p) in
  interference_graph' g p liveness
  
			 
(** Graph coloring. *)

let colorize_graph g = IGraphColoring.colorize g

(** Register allocation directed by the graph coloring. *)
let rec register_allocation coloring p =
  List.map (register_allocation_definition coloring) p

and register_allocation_definition coloring = function
  | DValue (i, block) -> 
     let local, li= block in
     let new_li =
       List.map (register_allocation_li local coloring) li
     in
     DValue (i, (local, new_li))
      
  | DFunction (idf, i, block) ->
     let local, li= block in
     let new_li =
       List.map (register_allocation_li local coloring) li
     in
     DFunction (idf, i, (local, new_li))
	    
  | DExternalFunction _ as de -> de

and register_allocation_li local coloring = function
    
  | l, Call (lv, rv, rvl) ->
     let new_lv =
       register_allocation_lvalue local coloring lv
     in
     let new_rv =
       register_allocation_rvalue local coloring rv
     in
     let new_rvl =
       List.map (register_allocation_rvalue local coloring) rvl
     in
     l, Call (new_lv, new_rv, new_rvl)
	     
  | l, TailCall (rv, rvl) ->
     let new_rv =
       register_allocation_rvalue local coloring rv
     in
     let new_rvl =
       List.map (register_allocation_rvalue local coloring) rvl
     in
     l, TailCall (new_rv, new_rvl)
		 
  | l, Ret rv ->
     let new_rv =
       register_allocation_rvalue local coloring rv
     in
     l, Ret new_rv
	    
  | l, Assign (lv,op,rvl) ->
     let new_lv =
       register_allocation_lvalue local coloring lv
     in
     let new_rvl =
       List.map (register_allocation_rvalue local coloring) rvl
     in
     l, Assign (new_lv, op, new_rvl)
     
  | l, ConditionalJump (c,rvl,l1,l2) ->
     let new_rvl =
       List.map (register_allocation_rvalue local coloring) rvl
     in
     l, ConditionalJump (c, new_rvl, l1, l2)

     
  | l, Switch (rv, la, lo) ->
     let new_rv =
       register_allocation_rvalue local coloring rv
     in
     l, Switch (new_rv, la, lo)
	          
  (* aucun changement *)
  | _, Jump _ as li -> li
  | _, Comment _ as li -> li
  | _, Exit as li -> li

and register_allocation_lvalue local coloring lv =
  match lv with
  | `Variable v
       when (try List.exists (fun x -> v = x) local with _ -> false) ->

     (try
     (match IGraphColoring.color_of_node coloring lv with
      | Some (RId r) -> `Register (RId ("$" ^ r))
      | _ -> lv)
       with _ -> `Variable v)
       
  | _ -> lv
							 
and register_allocation_rvalue local coloring = function
    
  | `Variable v as lv
       when (try List.exists (fun x -> v = x) local with _ -> false) ->

     (try
     (match IGraphColoring.color_of_node coloring lv with
      | Some (RId r) -> `Register (RId ("$" ^ r))
      | _ -> lv)
       with _ -> `Variable v)
       
  | `Register _ as lv ->
     (match IGraphColoring.color_of_node coloring lv with
      | Some (RId r) -> `Register (RId ("$" ^ r))
      | _ -> lv)

		   
  | _ as rv -> rv




		 
  (** Putting all together. *)
let translate p =

  (* analyse de vivacité *)
  let liveness = liveness_analysis p in

  (* construction du graph d'interphérence *)
  let igraph   = interference_graph p liveness in

  (* coloration de graph *)
  let coloring = colorize_graph igraph in

  (* check si le graph est correctement colorié *)
  IGraphColoring.check_coloring' igraph coloring;

  (* traduit le program avec les nouveau registre *)
  register_allocation coloring p
