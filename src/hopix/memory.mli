(* Memory implements a heap for record values. *)

(* ['v t] is the type for a memory containing records with fields 
   of type ['v]. *)
type 'v t

(* An [address] is a location in memory. *)
type address

(* [fresh ()] returns a fresh empty memory. *)
val fresh : unit -> 'v t

(* [allocate m r] extends [m] with a fresh location to store the record
   [r] represented as an associative list. It returns this fresh location
   and the new extended memory. *)
val allocate : 'v t -> (HopixAST.label * 'v) list -> address * 'v t

(* [read m a l] returns the value of the field [l] of the record
   located at the address [a] in the memory [m]. Precondition: the
   record and its field actually exist at the address [a]. *)
val read : 'v t -> address -> HopixAST.label -> 'v

(* [read_block m a] returns the record located at [a] in memory [m]
   in the form of an associative list. *)
val read_block : 'v t -> address -> (HopixAST.label * 'v) list

(* [write m a l v] returns a new memory in which the field [l] of
   the record located at [a] in [m] is updated with value [v]. *)
val write : 'v t -> address -> HopixAST.label -> 'v -> 'v t
