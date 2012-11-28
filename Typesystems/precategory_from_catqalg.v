Add Rec LoadPath "../Generalities".
Add Rec LoadPath "../hlevel1".
Add Rec LoadPath "../hlevel2".

Require Import uu0.
Require Import hSet.
Require Import catqalg.
Require Import precategories.

Notation "a == b" := (paths a b) (at level 70, no associativity).
Notation "! p " := (pathsinv0 p) (at level 50).
Notation "p @ q" := (pathscomp0 p q) (at level 60, right associativity).


(** * Precategory from a quasi-alg. category *)

(** we construct a precategory from a given quasi-alg. category.
    all the work is actually done in the file on quasi-alg. 
    categories *)


Section precat_from_catqalg.

Variable C : catqalg.

Definition precategory_ob_mor_from_catqalg : precategory_ob_mor .
(*    tpair _ (catqalgobjects C) (fun a b => catqalghomset a b). *)
Proof.
exists (catqalgobjects C).
exact (fun a b => catqalghomset a b).
Defined.

Definition precategory_data_from_catqalg : precategory_data.
Proof.
exists precategory_ob_mor_from_catqalg.
exists (catqalghomid (C:=C)).
exact (@catqalghomcomp C).
Defined.


Definition precategory_from_catqalg : precategory.
Proof.
exists precategory_data_from_catqalg.
assert (H:forall (a b : precategory_objects precategory_data_from_catqalg)
        (f : precategory_morphisms a b),
      precategory_compose (precategory_identity a) f == f).
simpl.
apply catqalghom_id_left.
assert (H':forall (a b : precategory_objects precategory_data_from_catqalg)
        (f : precategory_morphisms a b),
      precategory_compose f (precategory_identity b) == f).
simpl.
apply catqalghom_id_right.
exists (dirprodpair H H').
simpl.
unfold precategory_compose. simpl.
apply catqalghom_assoc.
Defined.

End precat_from_catqalg.













