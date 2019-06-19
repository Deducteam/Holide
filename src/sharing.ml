(** Functor building an implementation of shared terms.
    This code is inspired by the hashconsing module of J.-C. Filiatre:
    https://www.lri.fr/~filliatr/software.en.html **)

type id = int

module type HashedType =
sig

  type t

  val equal : t -> t -> bool

  val hash : t -> int

end

module Make(H : HashedType) :
sig

  val mem : H.t -> bool

  (** If the node is not in the table, generate a new [id] and associate it
      with the node. Return the [id] associated with [node]. *)
  val add : H.t -> id

  (** Return the [id] associated with [node]. *)
  val find : H.t -> id
  
  val clear : H.t -> unit
  
  val size : H.t -> int

end =
struct

  let table = Hashtbl.create 10007

  let mem node = Hashtbl.mem table node

  let add node =
    if not (Hashtbl.mem table node)
    then
    begin
    Hashtbl.add table node (Hashtbl.length table);
    end;
    Hashtbl.find table node

  let find node = 
    Hashtbl.find table node
  
  let clear node = 
    Hashtbl.reset table
  
  let size node = 
    Hashtbl.length table

end

