Add Rec LoadPath "../Generalities".
Add Rec LoadPath "../hlevel1".
Add Rec LoadPath "../hlevel2".

Require Import basic_lemmas_which_should_be_in_uu0.
Require Import uu0.
Require Import hProp.
Require Import hSet.
Require Import precategories.
Require Import precategory_of_hsets.


Notation "a == b" := (paths a b) (at level 70, no associativity).
Notation "! p " := (pathsinv0 p) (at level 50).
Notation "p @ q" := (pathscomp0 p q) (at level 60, right associativity).

Notation FUN := precategory_fun_precategory.
Notation HSET := hset_precategory.


Definition eval_on_obj (C : precategory) (c : precategory_objects C):
   precategory_objects (FUN C HSET) -> precategory_objects HSET.
Proof.
  intro F. simpl in *;
  exact (F c).
Defined.


Definition eval_on_obj (C : precategory) (c : precategory_objects C)   
  precategory_ob_mor_fun (FUN C HSET) HSET.
exists (fun F : precategory_objects (FUN C HSET) => F c).


Definition eval (C : precategory) : precategory_fun C (FUN (FUN C HSET) HSET).



  