(* Memory implements a heap for blocks. *)

(* ['v t] is the type for a memory containing blocks with cells of
   type ['v]. *)
type 'v t

(* An [address] is a location in memory. *)
type address

(* [fresh ()] returns a fresh empty memory. *)
val fresh : unit -> 'v t

(* [allocate m n d] extends [m] with a fresh location to store a block
   of size [n]. It returns this fresh location and the new extended
   memory. *)
val allocate : 'v t -> Int32.t -> 'v -> address * 'v t

(* [read m a i] returns the value of the i-th cell of the block
   located at the address [a] in the memory [m]. Precondition: the
   block and its cell actually exist at the address [a]. *)
val read : 'v t -> address -> Int32.t -> 'v
val read_block : 'v t -> address -> 'v array
  
(* [write m a i v] returns a new memory in which the i-th cell of
   the block located at [a] in [m] is updated with value [v]. *)
val write : 'v t -> address -> Int32.t -> 'v -> 'v t
