(* HOL types *)

Parameter type : Type.

Parameter bool : type.
Parameter ind  : type.
Parameter arr : type -> type -> type.

(* HOL terms *)

Parameter term : type -> Type.

Parameter lam : forall (a : type), forall (b : type), (term a -> term b) -> term (arr a b).
Parameter app : forall (a : type), forall (b : type), term (arr a b) -> term a -> term b.
Parameter eq : forall (a : type), term (arr a (arr a bool)).
Parameter select : forall (a : type), term (arr (arr a bool) a).

Definition EQ : forall (a : type), term a -> term a -> term bool :=
  fun (a : type) => fun (x : term a) => fun (y : term a) => app a bool (app a (arr a bool) (eq a) x) y.
Definition SELECT : forall (a : type), term (arr a bool) -> term a :=
  fun (a : type) => fun (p : term (arr a bool)) => app (arr a bool) a (select a) p.

Definition true : term bool :=
  EQ (arr bool bool) (lam bool bool (fun (p : term bool) => p)) (lam bool bool (fun (p : term bool) => p)).
Definition witness : forall (a : type), term a :=
  fun (a : type) => SELECT a (lam a bool (fun (x : term a) => true)).

(* HOL proofs *)

Parameter proof : term bool -> Type.

Parameter REFL : forall (a : type), forall (t : term a),
  proof (EQ a t t).
Parameter ABS_THM : forall (a : type), forall (b : type), forall (f : (term a -> term b)), forall (g : (term a -> term b)),
  (forall (x : term a), proof (EQ b (f x) (g x))) ->
  proof (EQ (arr a b) (lam a b f) (lam a b g)).
Parameter APP_THM : forall (a : type), forall (b : type), forall (f : term (arr a b)), forall (g : term (arr a b)), forall (x : term a), forall (y : term a),
  proof (EQ (arr a b) f g) ->
  proof (EQ a x y) ->
  proof (EQ b (app a b f x) (app a b g y)).
Parameter PROP_EXT : forall (p : term bool), forall (q : term bool),
  (proof q -> proof p) ->
  (proof p -> proof q) ->
  proof (EQ bool p q).
Parameter EQ_MP : forall (p : term bool), forall (q : term bool),
  proof (EQ bool p q) ->
  proof p ->
  proof q.
Parameter BETA_CONV : forall (a : type), forall (b : type), forall (f : term a -> term b), forall (x : term a),
  proof (EQ b (app a b (lam a b f) x) (f x)).
  
