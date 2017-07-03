type address = int
type 'v t = (HopixAST.label * 'v) list array ref

let addr = ref 0 
				  
let fresh () = addr := 0 ; ref (Array.make 100 [])
			  
let read m a l =
  List.assoc l !m.(a)
  
let read_block m a = !m.(a)

let write m a l v =

  let rec aux l v = function
    | [] -> []
    | (l', v'):: tl when l = l' ->
       (l, v) :: tl
    | h :: tl ->
       h :: aux l v tl
  in

  !m.(a) <- aux l v (!m.(a)); m
			      
       
let allocate (m: 'v t) (r : (HopixAST.label * 'v) list) =
  !m.(!addr) <- r ;
  addr := !addr + 1;
  ((!addr)-1,m)
