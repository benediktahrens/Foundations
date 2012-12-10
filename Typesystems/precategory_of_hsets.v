Add Rec LoadPath "../Generalities".
Add Rec LoadPath "../hlevel1".
Add Rec LoadPath "../hlevel2".
Add Rec LoadPath "../Proof_of_Extensionality".

Require Import basic_lemmas_which_should_be_in_uu0.
Require Import uu0.
Require Import hProp.
Require Import hSet.
Require Import precategories.
Require Import HLevel_n_is_of_hlevel_Sn.
Require Import funextfun.

Notation "a == b" := (paths a b) (at level 70, no associativity).
Notation "! p " := (pathsinv0 p) (at level 50).
Notation "p @ q" := (pathscomp0 p q) (at level 60, right associativity).

Local Notation "a --> b" := (precategory_morphisms a b)(at level 50).




(** * Preategory of hSets *)

Lemma isaset_set_fun_space (A B : hSet) : isaset (A -> B).
Proof.
  change isaset with (isofhlevel 2).
  apply impred.
  apply (fun _ => B).
Qed.

Definition set_fun_space (A B : hSet) : hSet := 
  hSetpair _ (isaset_set_fun_space A B).

Definition hset_precategory_ob_mor : precategory_ob_mor :=
  tpair (fun ob : UU => ob -> ob -> hSet) hSet 
        (fun A B : hSet => set_fun_space A B).

Definition hset_precategory_data : precategory_data :=
  precategory_data_pair hset_precategory_ob_mor (fun (A:hSet) (x : A) => x) 
     (fun (A B C : hSet) (f : A -> B) (g : B -> C) (x : A) => g (f x)).

Lemma is_precategory_hset_precategory_data :
  is_precategory hset_precategory_data.
Proof.
  repeat split; simpl.
  intros a b f.
  apply funextfunax; intros;
  apply idpath.
  intros;
  apply funextfunax; intros;
  apply idpath.
Qed.

Definition hset_precategory : precategory := 
  tpair _ _ is_precategory_hset_precategory_data.

Notation HSET := hset_precategory.

(* 
  Canonical Structure hset_precategory. :-)
*)

Lemma hset_iso_is_equiv (A B : precategory_objects HSET) 
   (f : iso_precat A B) : isweq (pr1 f).
Proof.
  destruct f as [f fax]; simpl in *.
  apply (gradth _ (pr1 fax)).
  destruct fax as [g [eta eps]]; simpl in *.
  unfold precategory_compose, precategory_identity in *; 
  simpl in *.
  intro x.
  apply (happly _ _ _ _ eta x).
  destruct fax as [g [eta eps]]; simpl in *.
  unfold precategory_compose, precategory_identity in *; 
  simpl in *.
  intro x.
  apply (happly _ _ _ _ eps x).
Qed.
  

Lemma hset_iso_equiv (A B : precategory_objects HSET) :
  iso_precat A B -> weq (pr1 A) (pr1 B).
Proof.
  intro f.
  exists (pr1 f).
  apply hset_iso_is_equiv.
Defined.

Lemma hset_equiv_is_iso (A B : hSet) 
      (f : weq (pr1 A) (pr1 B)) :
           is_precat_isomorphism (C:=HSET) (pr1 f).
Proof.
  exists (invmap f).
  simpl.
  set (H := homotweqinvweq f).
  set (H':= homotinvweqweq f).
  split; simpl.
  apply funextfunax; intro x; simpl in *.
  unfold precategory_compose, precategory_identity; simpl.
  apply H'.
  apply funextfunax; intro x; simpl in *.
  unfold precategory_compose, precategory_identity; simpl.
  apply H.
Qed.

Lemma hset_equiv_iso (A B : precategory_objects HSET) :
    weq (pr1 A) (pr1 B) -> iso_precat A B.
Proof.
  intro f.
  simpl in *.
  exists (pr1 f).
  apply hset_equiv_is_iso.
Defined.

Lemma hset_iso_equiv_is_equiv (A B : precategory_objects HSET) :
      isweq (hset_iso_equiv A B).
Proof.
  apply (gradth _ (hset_equiv_iso A B)).
  intro f.
  assert (H : pr1 (hset_equiv_iso A B (hset_iso_equiv A B f)) ==
              pr1 f).
  simpl. 
  apply idpath.
  apply (total2_paths H).
  apply proofirrelevance.
  apply isaprop_is_precat_isomorphism.
  intro g.
  assert (H : pr1 (hset_iso_equiv A B (hset_equiv_iso A B g)) == 
              pr1 g).
  simpl. 
  apply idpath.
  apply (total2_paths H).
  apply proofirrelevance.
  apply isapropisweq.
Qed.

Definition hset_iso_equiv_weq (A B : precategory_objects HSET) :
  weq (iso_precat A B) (weq (pr1 A) (pr1 B)).
Proof.
  exists (hset_iso_equiv A B).
  apply hset_iso_equiv_is_equiv.
Defined.

Lemma hset_equiv_iso_is_equiv (A B : precategory_objects HSET) :
      isweq (hset_equiv_iso A B).
Proof.
  apply (gradth _ (hset_iso_equiv A B)).
  intro f.
  assert (H : pr1 (hset_iso_equiv A B (hset_equiv_iso A B f)) ==
              pr1 f).
  simpl. 
  apply idpath.
  apply (total2_paths H).
  apply proofirrelevance.
  apply isapropisweq.
  intro g.
  assert (H : pr1 (hset_equiv_iso A B (hset_iso_equiv A B g)) == 
              pr1 g).
  simpl. 
  apply idpath.
  apply (total2_paths H).
  apply proofirrelevance.
  apply isaprop_is_precat_isomorphism.
Qed.

Definition hset_equiv_iso_weq (A B : precategory_objects HSET) :
  weq (weq (pr1 A) (pr1 B))(iso_precat A B).
Proof.
  exists (hset_equiv_iso A B).
  apply hset_equiv_iso_is_equiv.
Defined.
  

Definition univalenceweq (X X' : UU) : weq (X == X') (weq X X') :=
   tpair _ _ (univalenceaxiom X X').

Definition hset_id_iso_weq (A B : precategory_objects HSET) :
  weq (A == B) (iso_precat A B) :=
  weqcomp (UA_for_hSets A B) (hset_equiv_iso_weq A B).


Lemma bla (A : UU) (a : A):
  eqweqmap  (idpath A) a == a.
Proof.
  simpl.
  apply idpath.
Defined.


Lemma hset_id_iso_weq_is (A B : precategory_objects HSET):
    precat_paths_to_iso A B == pr1 (hset_id_iso_weq A B).
Proof.
  apply funextfunax.
  intro p.
  elim p.
  simpl.
  assert (H : pr1 (identity_iso_precat A) ==
              pr1 (hset_equiv_iso A A (pr1 (UA_for_hSets A A) (idpath A)))).
  
             simpl.
(*  destruct (UA_for_hSets A A) as [f fax].*)
  simpl in *.
  apply funextfun.
  unfold precategory_identity. simpl.
  intro x; 
  simpl. clear p. Check pr1.
  destruct A as [A As].
  simpl. apply idpath.
  
  apply (total2_paths H).
  simpl.
  Check (pr2 (hset_equiv_iso A A (pr1 (UA_for_hSets A A) (idpath A)))).
  apply proofirrelevance.
  simpl.
  apply isaprop_is_precat_isomorphism.
Defined.


Lemma is_weq_precat_paths_to_iso_hset (A B : precategory_objects HSET):
   isweq (precat_paths_to_iso A B).
Proof.
  rewrite hset_id_iso_weq_is.
  apply (hset_id_iso_weq A B).
Qed.

Lemma is_saturated_HSET : is_saturated HSET.
Proof.
  unfold is_saturated.
  apply is_weq_precat_paths_to_iso_hset.
Qed.









  
  set (H' := @uip 
((fun f : A --> A => is_precat_isomorphism f)
         (pr1 (hset_equiv_iso A A (pr1 (UA_for_hSets A A) (idpath A)))))).
         simpl in H'.
         apply H'.
  apply uip.

  simpl.
  
  assert (H: f (idpath A) == idpath (@pr1 UU (fun X => isaset X) A)).
  destruct A as [A Aisset]; simpl in *.
  change (idpath
  About identity_refl.
  unfold identity_refl.
  destruct (idpath A).
  simpl.

  unfold UA_for_hSets.
  simpl.
              pr1 (hset_id_iso_weq A B)).
  

  exists (pr1 fax).
   (f : iso_precat A B) : isweq (pr1 f).
Proof.
  destruct f as [f fax]; simpl in *.
  apply (gradth _ (pr1 fax)).
  destruct fax as [g [eta eps]]; simpl in *.
  unfold precategory_compose, precategory_identity in *; 
  simpl in *.
  intro x.
  apply (happly _ _ _ _ eta x).
  destruct fax as [g [eta eps]]; simpl in *.
  unfold precategory_compose, precategory_identity in *; 
  simpl in *.
  intro x.
  apply (happly _ _ _ _ eps x).
Qed.
  

Lemma hset_iso_equiv (A B : precategory_objects HSET) :
  iso_precat A B -> weq (pr1 A) (pr1 B).

Lemma is_saturated_hset_precategory : is_saturated hset_precategory.
Proof.
  unfold is_saturated.
  simpl.
  intros A B.
  set (H := UA_for_HLevels 2 A B).
  destruct H as [H H'].
  unfold isweq.
  simpl.
  intro f.
  unfold precat_paths_to_iso.
  simpl.














