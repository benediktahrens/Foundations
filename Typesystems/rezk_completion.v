
(************************************************************

Benedikt Ahrens and Chris Kapulkin
january 2013


************************************************************)


(************************************************************

Contents : Rezk completion

************************************************************)


Add Rec LoadPath "../Generalities".
Add Rec LoadPath "../hlevel1".
Add Rec LoadPath "../hlevel2".
Add Rec LoadPath "../Proof_of_Extensionality".

Require Import basic_lemmas_which_should_be_in_uu0.
Require Import uu0.
Require Import hProp.
Require Import hSet.

Require Import AXIOM_dep_funext.

Require Import precategories.
Require Import precategory_of_hsets.
Require Import yoneda.
Require Import precategory_whiskering.
Require Import precategory_lemma62.
Require Import precategory_lemma64.

Notation "a == b" := (paths a b) (at level 70, no associativity).
Notation "! p " := (pathsinv0 p) (at level 50).
Notation "p @ q" := (pathscomp0 p q) (at level 60, right associativity).

Ltac pathvia b := (apply (@pathscomp0 _ _ b _ )).

Section rezk.

Variable A : precategory.

Definition Rezk_completion : sat_precat.
Proof.
  exists (full_img_sub_precategory (yoneda A)).
  apply is_saturated_full_subcat.
  apply is_saturated_functor_category.
  apply is_saturated_HSET.
Defined.

Definition Rezk_eta : precategory_fun A Rezk_completion.
Proof.
  apply (precategory_fun_full_img (yoneda A)).
Defined.

Lemma Rezk_eta_is_fully_faithful : fully_faithful Rezk_eta.
Proof.
  apply (precategory_fun_full_img_fully_faithful_if_fun_is _ _ (yoneda A)).
  apply yoneda_fully_faithful.
Qed.

Lemma Rezk_eta_essentially_surjective : essentially_surjective Rezk_eta.
Proof.
  unfold Rezk_eta.
  unfold essentially_surjective.
  simpl.
  intro b.
  













