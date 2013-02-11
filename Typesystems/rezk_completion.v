
(** **********************************************************

Benedikt Ahrens and Chris Kapulkin
january 2013


************************************************************)


(** **********************************************************

Contents : Rezk completion

 - Construction of the Rezk completion via Yoneda

 - Universal property of the Rezk completion

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
Require Import functors_transformations.
Require Import category_hset.
Require Import yoneda.
Require Import sub_precategories.
Require Import equivalences.
Require Import whiskering.
Require Import precomp_fully_faithful.
Require Import precomp_ess_surj.

Notation "a == b" := (paths a b) (at level 70, no associativity).
Notation "! p " := (pathsinv0 p) (at level 50).
Notation "p @ q" := (pathscomp0 p q) (at level 60, right associativity).

Ltac pathvia b := (apply (@pathscomp0 _ _ b _ )).

(** * Construction of the Rezk completion via Yoneda *)

Section rezk.

Variable A : precategory.

Definition Rezk_completion : category.
Proof.
  exists (full_img_sub_precategory (yoneda A)).
  apply is_category_full_subcat.
  apply is_category_functor_category.
  apply is_category_HSET.
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
  apply (precategory_fun_full_img_essentially_surjective _ _ (yoneda A)).
Qed.

End rezk.

(** * Universal property of the Rezk completion *)

Section rezk_universal_property.

Variables A C : precategory.
Hypothesis Ccat : is_category C.

Lemma pre_comp_rezk_eta_is_fully_faithful :
    fully_faithful (pre_whisker_functor A (Rezk_completion A) C (Rezk_eta A)).
Proof.
  apply pre_whisker_with_ess_surj_and_fully_faithful_is_fully_faithful.
  apply Rezk_eta_essentially_surjective.
  apply Rezk_eta_is_fully_faithful.
Qed.

Lemma pre_comp_rezk_eta_is_ess_surj :
   essentially_surjective (pre_whisker_functor A (Rezk_completion A) C (Rezk_eta A)).
Proof.
  apply pre_whisker_essentially_surjective.
  assumption.
  apply Rezk_eta_essentially_surjective.
  apply Rezk_eta_is_fully_faithful.
Qed.

Theorem Rezk_eta_Universal_Property : 
  isweq (pre_whisker_functor A (Rezk_completion A) C (Rezk_eta A)).
Proof.
  apply equiv_of_cats_is_weq_of_objects.
  apply is_category_functor_category; 
  assumption.
  apply is_category_functor_category; 
  assumption.
  
  apply rad_equivalence_of_precats.
  apply is_category_functor_category; 
  assumption.
  apply pre_comp_rezk_eta_is_fully_faithful.
  apply pre_comp_rezk_eta_is_ess_surj.
Qed.

End rezk_universal_property.
  
  














