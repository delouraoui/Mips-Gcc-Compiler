type address = Addr of Int32.t

module M = Map.Make (struct type t = address let compare = compare end)

type 'v t = 'v array M.t

let fresh () =
  M.empty

let read_block m a =
  M.find a m

let read m a i =
  (M.find a m).(Int32.to_int i)

let write m a i v =
  let b = M.find a m in
  let b' = Array.copy b in
  b'.(Int32.to_int i) <- v;
  M.add a b' m

let allocate m n d =
  let n = Int32.to_int n in
  let rec gen () =
    let a = Addr (Int32.of_int (Random.bits ())) in
    if M.mem a m then
      gen ()
    else
      (a, M.add a (Array.make n d) m)
  in
  gen ()
