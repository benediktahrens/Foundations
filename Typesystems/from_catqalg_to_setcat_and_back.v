Add Rec LoadPath "../Generalities".
Add Rec LoadPath "../hlevel1".
Add Rec LoadPath "../hlevel2".


Require Import basic_lemmas_which_should_be_in_uu0.
Require Import hSet.
Require Import catqalg.
Require Import precategories.
Require Import catqalg_from_setcategory.
Require Import precategory_from_catqalg.

(*
Require Import pathnotations.
Import pathnotations.PathNotations.
*)

Notation "a == b" := (paths a b) (at level 70, no associativity).
Notation "! p " := (pathsinv0 p) (at level 50).
Notation "p @ q" := (pathscomp0 p q) (at level 60, right associativity).


Lemma hSet_eq (X X' : hSet) : pr1 X == pr1 X' -> X == X'.
Proof.
  intro H.
  apply (total2_paths H).
  apply proofirrelevance.
  apply isapropisaset.
Defined.

(*

Lemma catqalg_from_precat_from_catqalg (C : catqalg) :
   catqalg_from_setcat (setcategory_from_catqalg C) == C.
Proof.
  apply catqalg_eq_if_catqalg_data.
  destruct C as [CD Cax].
  simpl.
  assert (H : pr1 (catqalg_data_from_setcategory
                (setcategory_from_catqalg {| pr1 := CD; pr2 := Cax |})) 
                     ==  pr1 CD).
  simpl.
  destruct CD as [Cell Ccomp]; simpl in *.
  assert (H':
      pr1 (cell_data_from_setcategory
               (setcategory_from_catqalg
           {| pr1 := {| pr1 := Cell; pr2 := Ccomp |}; pr2 := Cax |}) )
        == pr1 Cell ).
  simpl.
  destruct Cell as [C1 C2]. simpl in *.
  destruct C1 as [ob mor]. simpl in *.
  apply pathsdirprod; simpl in *. 
  unfold setcategory_objects_set. simpl.
  simpl.
  destruct ob. simpl.
  apply idpath.
  apply hSet_eq.
  simpl.
  unfold precategory_total_morphisms.
  simpl.
  clear Cax.
  clear Ccomp.
  destruct mor as [mor p].
  simpl in *.
  apply univalence
  unfold setcategory_total_morphisms_set.
  simpl. Check mor.
  destruct mor.
  simpl.
  apply idpath.





  apply 
  clear Cax.

*)