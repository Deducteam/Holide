(** Creating and using the database of articles inputs and outputs *)

open Graph

module Dep =
  struct
  
	module Str = struct
		type t = string
		let compare = String.compare
		let hash = Hashtbl.hash
		let equal = String.equal
	end
	
	include Imperative.Digraph.Concrete(Str)
  end

let dep = Dep.create()

module OrderedDep  = Topological.Make(Dep)

(* Adding a file to the graph *)

let add_mod mod_name =
	Dep.add_vertex dep mod_name

(* Adding dependencies *)

let add_dep mod_name dep_name =
	Dep.add_edge dep dep_name mod_name

let fill_dep l =
	List.iter add_mod l;
	Hashtbl.iter add_dep (Type.deps)

(* Find order *)

let ordereddep f g = OrderedDep.iter f g

(* Number of added files *)

let number_dep () = Dep.nb_vertex dep
