

Add Rec LoadPath "../Generalities".
Add Rec LoadPath "../hlevel1".
Add Rec LoadPath "../hlevel2".

Require Import basic_lemmas_which_should_be_in_uu0.
Require Import uu0.
Require Import hProp.
Require Import hSet.

Notation "a == b" := (paths a b) (at level 70, no associativity).
Notation "! p " := (pathsinv0 p) (at level 50).
Notation "p @ q" := (pathscomp0 p q) (at level 60, right associativity).


Axiom dep_funextfunax : forall (A : UU)(B : A -> UU) (f g: forall a, B a),
            (forall x, f x == g x) -> f == g.

(*
Axiom dep_funextfunax_type : forall (A : Type) (B : A -> Type) (f g : forall a, B a),
       (forall x, f x == g x) -> f == g.
*)

(**   dependent funext

toforallpaths
isweqtoforallpaths

*)

(*
Definition dep_maponpaths (A : UU) (B : A -> UU) (f g : forall a, B a) :
     f == g -> forall a, f a == g a.

Search (forall a , _ ?a == _ ?a).

Print maponpaths.
*)