(** This module implements a generic graph coloring algorithm. *)

module type ColorsSig = sig
  type t
  (** [all] enumerates the available colors. *)
  val all : t list
  val cardinal : int
  val to_string : t -> string
end

module Make
  (EdgeLabel : sig
    include Graph.EdgeLabelSig
    (** A conflict edge imposes a distinct color on its two nodes. *)
    val conflict   : t
    (** A preference edge indicates that two nodes should have the
	same color if possible. *)
    val preference : t
  end)
  (NodeLabel : Graph.NodeLabelSig)
  (Colors : ColorsSig)
  =
struct

  module Graph = Graph.Make (EdgeLabel) (NodeLabel)

  module NodeLabelMap = Map.Make (NodeLabel)

  (** A coloring maps every node label to a color option. *)
  type t = Colors.t option NodeLabelMap.t

  (** The empty coloring. *)
  let empty = NodeLabelMap.empty

  (** Return the color of the node [n] in the coloring. *)
  let color_of_node coloring n =
    try NodeLabelMap.find n coloring with Not_found -> None

  let all_color = Colors.all |> List.map Colors.to_string

  (** Assign the color [c] to the node [n] in the [coloring]. *)
  let assign_color g n c coloring =
    List.fold_left (fun coloring n ->
      NodeLabelMap.add n (Some c) coloring
    ) coloring (Graph.all_labels g n)

  (** Assign no color to the node [n] in the [coloring]. *)
  let assign_no_color g n coloring =
    List.fold_left (fun coloring n ->
      NodeLabelMap.add n None coloring
    ) coloring (Graph.all_labels g n)

  (** [InvalidColoring c] is raised if [c] is not a valid coloring. *)
  exception InvalidColoring of t


  (** [check_coloring g c] checks if [c] is a valid coloring for [g]
      i.e. that every pair of conflicting nodes have different
      colors. *)

  (** Version 1 du check_coloring *)

  let print_all_colors () =
    Colors.all
    |> List.iter (fun x -> print_endline (Colors.to_string x))

  let print_node n = print_endline (NodeLabel.to_string n)

  let colors_of_nregister nreg =
    let str = NodeLabel.to_string nreg in
    let str =
      if str.[1] = '$' then
	String.sub str 2 (String.length str -2)
      else 
	String.sub str 1 (String.length str - 1)
    in
    let lcolor =
      List.filter (fun x -> Colors.to_string x = str) Colors.all
    in
    match lcolor with
    | [] -> None
    | a :: _ -> Some a

  let is_noderegister n =
    let str  = NodeLabel.to_string n in
    str.[0] = '$'

  let degree_of_node g n =
    List.length (Graph.neighbours g EdgeLabel.conflict n)		     
				 
  let check_edge_coloring g c = (* check pour une arete *)
    
    let one_edge =
      Graph.pick_edge g EdgeLabel.conflict
    in (* pick une arete conflict du graph *)
    
    match one_edge with

    (* si il y en une *)
    | Some (n1, n2) ->

       (* test la couleur *)
       (match color_of_node c n1, color_of_node c n2 with
	| None,_ | _,None -> ()
	| c1, c2 -> assert (c1 <> c2)) ;
       (* retourne un graphe ou l'arete est supprimé *)
       Some (Graph.del_edge g n1 EdgeLabel.conflict n2)

    (* si il n'y en a pas *)
    | None ->

       (* retourne None *)
       None

  let rec check_coloring' g c = (* check pour toute les aretes conflicts *)
    match check_edge_coloring g c with

    (* si il reste des arete conflicts *)
    | Some g' -> check_coloring' g' c

    (* si il n'y plus d'arete conflicts *)
    | None -> ()

  (** *)
				 
  let check_coloring g c =

    (* test si deux noeud sont bien de couleur differente *)
    let check_color_one_node n1 n2 c =
      match color_of_node c n1, color_of_node c n2 with
      | None,_ | _,None -> ()
      | Some c1, Some c2 -> assert (c1 <> c2)
    in
    
    let ledge = (* recupere toute les arete de conflit du graphe *)
      Graph.edges g EdgeLabel.conflict
    in

    (* iter sur toute les aretes de la liste est test si il sont de couleur differente *)
    List.iter (fun (n1,n2) -> check_color_one_node (List.hd n1) (List.hd n2) c) ledge
	      
  type pick_result =
    | EmptyGraph
    | SimplifiableNode of NodeLabel.t
    | PreferenceNodes of NodeLabel.t * NodeLabel.t
    | MaybeSpillNode of NodeLabel.t


  (** pick_register g : retourne un registre si il existe ou None
      si le graph ne contient aucun registre *)
  let rec pick_register g =

    (* on recupere un noeud de poid minimal qui n'a aucune arete de preference *)
    match Graph.min_degree g EdgeLabel.conflict EdgeLabel.preference with

    (* si c'est un registre alors on le recupere *)
    | Some (_, n) when (is_noderegister n) -> Some n

    (* si ce n'est pas un registre on réitere *)
    | Some (_, n) -> pick_register (Graph.del_node g n)

    (* si il n'existe aucun noeud sans arete de preference *)
    | None ->

       begin

	 (* on regarde si il n'existe une arete de preference *)
	 match Graph.pick_edge g EdgeLabel.preference with

	 (* si il en n'existe, on la supprime puis on reitere *)
	 | Some (n1, n2) ->
	    pick_register (Graph.del_edge g n1 EdgeLabel.preference n2)

	 (* si il n'en existe pas, c'est que le graph est vide *)
	 | None -> None
	 
       end

  (** colorize_register g, prend un argument un graph et retourne une coloration
      ou tout les registres sont colorié *)
  let rec colorize_register g =

    (* tente de recuperer un registre *)
    match pick_register g with

    (* si il y en a un on le colorie *)
    | Some n ->

       (* supprime le registre et colorie le reste du graph *)
       let coloring = colorize_register (Graph.del_node g n) in

       begin
       
	 (* recupere la couleur du registre *)
	 match colors_of_nregister n with
	 | None ->  assign_no_color g n coloring (* cas du registre $ra *)
	 | Some color ->
	    
	    (* retourne la coloration ou le registre est colorié *)
	    assign_color g n color coloring

       end
			 
    (* si il n'existe aucun registre, on renvoie la coloration vide *)
    | None -> empty
       

  (** retourne une variable qui ne possede aucun arete de preference, ou None
      si un tel noeud n'existe pas *)
  let rec pick_variable g =

    (* on recupere un noeud de poid minimal qui n'a aucune arete de preference *)
    match Graph.min_degree g EdgeLabel.conflict EdgeLabel.preference with

    (* si c'est un registe, alors on reitere *)
    | Some (_, n) when (is_noderegister n) ->
       pick_variable (Graph.del_node g n)

    (* si ce n'est pas un registre, on le retourne *)
    | Some (_, n) -> Some n

    (* sinon c'est que le graph est vide ou il n'existe aucun noeud sans arete P *)
    | None -> None

		
  (** [pick g] returns a node of degree less than the number [k] of
      colors and that is not in a preference relation if there is
      such node in [g]. Otherwise, it returns a pair of nodes that
      are in a preference relation. If there is no such pair, it
      returns a node that may be spilled. Otherwise, the graph is
      empty. *)	
  let pick g =

    let k = Colors.cardinal in
    
    (* pick une variable dans le graph sans arete de preference*)
    match pick_variable g with
            
    (* si il en existe une, et si le noeud est simplifiable *)
    | Some n when (degree_of_node g n < k) -> 
       SimplifiableNode n

    (* si le noeud n'est pas trivialement colorable *)
    | Some n ->

       begin

	 (* on regarde si il existe une arete de preference *)
	 match Graph.pick_edge g EdgeLabel.preference with

	 (* si une tel arete existe on la retorune *)
	 | Some (n1, n2) -> PreferenceNodes (n1, n2)

	 (* sinon on spill le noeud *)
	 | None -> MaybeSpillNode n

       end

    (* si il n'existe pas de tel noeud *)
    | None ->

       begin

	  (* on regarde si il existe une arete de preference *)
	 match Graph.pick_edge g EdgeLabel.preference with

	 (* si une tel arete existe on la retorune *)
	 | Some (n1, n2) -> PreferenceNodes (n1, n2)

	 (* sinon c'est que le graph est vide *)
	 | None -> EmptyGraph
	 
       end
       
		
  (** [colorize g] returns a coloring for [g]. *)
  let rec colorize g =
    colorize' g empty
	 
  and colorize' g coloring =

    (* pick une variable minimal du graph *)
    match pick g with
      
    (* Si le noeud peut etre simplifier *)
    | SimplifiableNode n ->
       simplify g n coloring
		
    (* Si on a une arete de preference *)
    | PreferenceNodes (n1, n2) ->

       (* si l'arete respecte le critere de briggs, on fusionne *)
       if briggs g n1 n2 then
	 fusion g n1 n2 coloring

       else (* sinon, on supprime l'arete et on pick de nouveau *) 
	 colorize' (Graph.del_edge g n1 EdgeLabel.preference n2) coloring
	      
    (* sinon on spill le node *)
    | MaybeSpillNode n ->
       spill g n coloring
	   
    (* si on a recuperer toute les variables *)
    | EmptyGraph ->

       (* on colorie tout les registre *)
       colorize_register g

  and available_colors not_those_colors all_color =
    List.filter (fun x -> not (List.exists (fun y -> x = y) not_those_colors)) all_color
   

  and color_of_lnode coloring lnode =
    match color_of_node coloring (List.hd lnode) with
    | Some s -> [ s ]
    | None -> []

		
  (** [briggs g n1 n2] returns true iff in [g'] the graph in which n1 and
      n2 are merged, the number of neighbours of the new node for n1 and n2
      has a number of non simplifiable node which is strictly less than the
      number of available colors. *)
  and briggs g n1 n2 =
    let k = Colors.cardinal in
    let d1 = degree_of_node g n1 in
    let d2 = degree_of_node g n2 in
    (d1 + d2 < k)

	     
  (** [george g n1 n2] returns true iff each neighbour of n1 that is in
      conflict with n1 and is not simplifiable is also in conflict with n2.
      (or the other way around). *)
  and george g n1 n2 =
    false

	     
  and merge g n1 n2 =
    let g = Graph.merge g n1 n2 in
    (**

	Let us write n the node for n1 and n2 in the new graph.
	If a node n' is both in preference and in conflict with n,
	then we remove the preference relation to keep only the
	conflicts. Otherwise, it would contradict the initial
        constraint.

    *)
    let i = Graph.neighbours' g [EdgeLabel.preference; EdgeLabel.conflict] n1 in
    List.fold_left (fun g ns ->
      Graph.del_edge g n1 EdgeLabel.preference (List.hd ns)
		   ) g i
		   
 	      	      
  and simplify g n coloring =
    
    let g' = Graph.del_node g n in
    let coloring = colorize' g'  coloring in
    
    (* voisins de n en arete de conflict *)
    let cneigh =
      Graph.neighbours g EdgeLabel.conflict n
    in
    
    (* recupere les couleurs à ne pas prendre *)
    let not_those_colors =
      List.map (fun x -> color_of_lnode coloring x) cneigh
      |> List.flatten
    in
    
    (* recupere les couleurs que l'on peut utiliser *)
    let a_colors =
      available_colors not_those_colors Colors.all
    in
    
    (* si une tel couleur existe, on l'assigne *)
    (match a_colors with
     | c' :: _ ->
	assign_color g n c' coloring 
     | _ -> assert false)

  and fusion g n1 n2 coloring =
    
    (* on fusionne les deux noeuds *)
    let g' = Graph.merge g n1 n2 in
    
    (* on colorie le graph avec les deux noeud fusionné *)
    let coloring = colorize' g' coloring in
    
    (* les noeud n1 et n2 aurons la couleur du noeud n1n2 *)
    let coloring =
      match color_of_node coloring n1 with
      | None -> assert false
      | Some s -> assign_color g n1 s coloring
    in
    let coloring =
      match color_of_node coloring n2 with
      | None -> assert false
      | Some s -> assign_color g n2 s coloring
    in
    coloring
      
  and spill g n coloring =

    (* on retire le noeud du graph *)
    let g' = Graph.del_node g n in

    (* on colorie le reste du graph *)
    let coloring = colorize' g'  coloring in

     (* voisins de n en arete de conflict *)
    let cneigh =
      Graph.neighbours g EdgeLabel.conflict n
    in
    
    (* recupere les couleurs à ne pas prendre *)
    let not_those_colors =
      List.map (fun x -> color_of_lnode coloring x) cneigh
      |> List.flatten
    in
    
    (* recupere les couleurs que l'on peut utiliser *)
    let a_colors =
      available_colors not_those_colors Colors.all
    in
    
    (* si une tel couleur existe, on l'assigne, sinon on spill *)
    (match a_colors with
     | c' :: _ -> assign_color g n c' coloring 
     | _ -> assign_no_color g n coloring)
   

end

let test () =
  (** The test parameters

      Customize them to test your implementation in an appropriate
      way.
  *)
  let show = false in
  let nb_test = 10 in
  let nb_color = 4 in
  let min_nodes = 100 and max_nodes = 200 in
  let freq_conflict = 0.2 and freq_preference =  0.3  in
  let random_seed = 33 in

  (** We instantiate the functor on simple nodes, edges and colors. *)
  let module NodeLabel = struct
    type t = string
    let compare = compare
    let to_string x = x
  end in
  let module EdgeLabel = struct
    type t = C | P
    let compare = compare
    let to_string = function C -> "<>" | P -> "="
    let preference = P
    let conflict = C
    let all = [ C ; P ]
  end in
  let module Colors = struct
    type t = int
    let all = ExtStd.List.range 0 (nb_color - 1)
    let cardinal = nb_color
    let to_string = string_of_int
  end
  in
  let module GC = Make (EdgeLabel) (NodeLabel) (Colors) in GC.(

    (** A function to generate a random graph. *)

    Random.init random_seed;
    let random_graph () =
      let nb_nodes = ExtStd.Random.int_in_range min_nodes max_nodes in
      let ns =
	List.map
	  (fun i -> "n" ^ string_of_int i)
	  (ExtStd.List.range 0 (nb_nodes - 1))
      in
      let g = List.fold_left (fun g n -> Graph.add_node g [n]) Graph.empty ns in
      List.fold_left (fun g n1 ->
	List.fold_left (fun g n2 ->
	  if n1 = n2
	  || Graph.are_connected g n1 EdgeLabel.C n2
	  || Graph.are_connected g n1 EdgeLabel.P n2
	  then
	    g
	  else if Random.float 1. < freq_conflict then
	    Graph.add_edge g n1 EdgeLabel.C n2
	  else if Random.float 1. < freq_preference then
	    Graph.add_edge g n1 EdgeLabel.P n2
	  else
	    g
	) g ns
      ) g ns
    in
    let show_coloring g coloring =
      Graph.show g (fun n ->
	try
	  Option.map Colors.to_string (color_of_node coloring n)
	with Not_found -> Some "!"
      )
    in
    let one_test () =
      let g = random_graph () in
      
      (** Show the graph! *)
      if show then Graph.show g (fun _ -> None);
      (** Compute the coloring. *)
      let coloring = colorize g in
      (** Show the coloring! *)
      if show then show_coloring g coloring;
      (** Check the coloring! *)
      try
	print_string "check coloring ";
	check_coloring' g coloring;
	check_coloring g coloring;
	print_endline "[OK]";
      with _ -> show_coloring g coloring; exit 1

    in
    for i = 0 to nb_test - 1 do
      one_test ()
    done
  )

