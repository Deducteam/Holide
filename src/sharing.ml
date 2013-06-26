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
  
(** If [node] is not in the table, [add define node] generates a new [id],
    calls [define id node], then assigns [node] to [id] in the table.
    Does nothing if [node] is already in the table.
    Returns [node] in both cases. *)
    val add : (id -> H.t -> unit) -> H.t -> H.t

(** [find node] returns the [id] associated to [node] in the table.
    Raises [Not_found] if [node] is not in the table. *)
    val find : H.t -> id

  end =
  struct
  
    let table = Hashtbl.create 10007
    
    let add define node =
      if not (Hashtbl.mem table node) then (
        let id = Hashtbl.length table in
        define id node;
        Hashtbl.add table node id);
      node
      
    let find node = Hashtbl.find table node
    
  end
