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
Require Import precategory_whiskering.

Notation "a == b" := (paths a b) (at level 70, no associativity).
Notation "! p " := (pathsinv0 p) (at level 50).
Notation "p @ q" := (pathscomp0 p q) (at level 60, right associativity).

Ltac pathvia b := (apply (@pathscomp0 _ _ b _ )).

Local Notation "a --> b" := (precategory_morphisms a b)(at level 50).
(*Local Notation "'hom' C" := (precategory_morphisms (C := C)) (at level 2).*)
Local Notation "f ;; g" := (precategory_compose f g)(at level 50).
Notation "[ C , D ]" := (precategory_fun_precategory C D).
Local Notation "# F" := (precategory_ob_mor_fun_morphisms F)(at level 3).


Section lemma64.

Variables A B C : precategory.
Hypothesis Csat : is_saturated C.
Variable H : precategory_objects [A, B].
Hypothesis p : essentially_surjective H.
Hypothesis Hff : fully_faithful H.

Section essentially_surjective.

Variable F : precategory_objects [A, C].

Section preimage.


Let X (b : precategory_objects B) := total2 (
 fun ck : 
  total2 (fun c : precategory_objects C =>
                forall a : precategory_objects A,
                     iso_precat (pr1 H a) b -> iso_precat (pr1 F a) c) =>
    forall t t' : total2 (fun a : precategory_objects A => iso_precat (pr1 H a) b),
          forall f : pr1 t --> pr1 t',
             (#(pr1 H) f ;; pr2 t' == pr2 t -> 
                    #(pr1 F) f ;; pr2 ck (pr1 t') (pr2 t') == pr2 ck (pr1 t) (pr2 t))).
(*
Let X (b : precategory_objects B) := 
  total2 (fun c : precategory_objects C =>
     total2 (fun k : forall a : precategory_objects A,
                     forall h : iso_precat (pr1 H a) b,
                                iso_precat (pr1 F a) c =>
      forall t t' : total2 (fun a : precategory_objects A => iso_precat (pr1 H a) b),
          forall f : pr1 t --> pr1 t',
             (#(pr1 H) f ;; pr2 t' == pr2 t -> 
                    #(pr1 F) f ;; k (pr1 t') (pr2 t') == k (pr1 t) (pr2 t)))).


Definition center_of_contr (b : precategory_objects B) 
    (anot : precategory_objects A)(hnot : iso_precat (pr1 H anot) b) : X b.
Proof.
  set (cnot := pr1 F anot).
  set (g := fun (a : precategory_objects A)(h : iso_precat (pr1 H a) b) =>
              (iso_from_fully_faithful_reflection _ _ H Hff _ _  
                  (iso_comp h (iso_inv_from_iso hnot)))).
  set (knot := fun (a : precategory_objects A)(h : iso_precat (pr1 H a) b) =>
                    precategory_fun_on_iso _ _ F _ _  (g a h)).
  exists (pr1 F anot).
  exists knot.
  intros t t' f.
  destruct t as [a h].
  destruct t' as [a' h'].
  simpl in *.
  intro star.
  rewrite <- (precategory_fun_comp _ _ F).
  apply maponpaths.
  Check (g a h).
  set (h2 := equal_transport_along_weq _ _
          (weq_from_fully_faithful _ _ _ Hff a anot)).
          apply h2. clear h2.
  simpl.
  rewrite precategory_fun_comp.
  set (H3 := homotweqinvweq (weq_from_fully_faithful _ _ _ Hff a' anot)).
  simpl in H3.
  unfold fully_faithful_inv_hom. simpl.
  rewrite H3.
  (*rewrite H3.*)
  clear H3.
  rewrite precategory_assoc.
  set (H3 := homotweqinvweq (weq_from_fully_faithful _ _ _ Hff a anot)).
  simpl in H3.
  unfold fully_faithful_inv_hom. simpl.
  rewrite H3.
  (*rewrite H3.*)
  clear H3.
  rewrite <- star.
  apply idpath.
Defined.
*)


Definition center_of_contr (b : precategory_objects B) 
    (anot : precategory_objects A)(hnot : iso_precat (pr1 H anot) b) : X b.
Proof.
  set (cnot := pr1 F anot).
  set (g := fun (a : precategory_objects A)(h : iso_precat (pr1 H a) b) =>
              (iso_from_fully_faithful_reflection _ _ H Hff _ _  
                  (iso_comp h (iso_inv_from_iso hnot)))).
  set (knot := fun (a : precategory_objects A)(h : iso_precat (pr1 H a) b) =>
                    precategory_fun_on_iso _ _ F _ _  (g a h)).
  simpl in *.
  exists (tpair _ (pr1 F anot) knot).
(*  exists (pr1 F anot).
  exists knot.
*)

  intros t t' f.
  destruct t as [a h].
  destruct t' as [a' h'].
  simpl in *.
  intro star.
  rewrite <- (precategory_fun_comp _ _ F).
  apply maponpaths.
  Check (g a h).
  set (h2 := equal_transport_along_weq _ _
          (weq_from_fully_faithful _ _ _ Hff a anot)).
          apply h2. clear h2.
  simpl.
  rewrite precategory_fun_comp.
  set (H3 := homotweqinvweq (weq_from_fully_faithful _ _ _ Hff a' anot)).
  simpl in H3.
  unfold fully_faithful_inv_hom. simpl.
  rewrite H3.
  (*rewrite H3.*)
  clear H3.
  rewrite precategory_assoc.
  set (H3 := homotweqinvweq (weq_from_fully_faithful _ _ _ Hff a anot)).
  simpl in H3.
  unfold fully_faithful_inv_hom. simpl.
  rewrite H3.
  (*rewrite H3.*)
  clear H3.
  rewrite <- star.
  apply idpath.
Defined.





Lemma lemma64_claim1 : forall b : precategory_objects B,
    iscontr (X b).
Proof.
  intro b.
  assert (HH : isaprop (iscontr (X b))).
  apply isapropiscontr.
  set (pbH := p b (tpair (fun x => isaprop x) (iscontr (X b)) HH)).
  simpl in *.
  apply pbH; clear pbH HH.
  intros [anot hnot].
  
  exists (center_of_contr b anot hnot).
  intro t.
  simpl in X.
  assert (Hpr1 : pr1 (center_of_contr b anot hnot) == pr1 t).
  set (w := isotoid _ Csat ((pr2 (pr1 t)) anot hnot) : 
          pr1 (pr1 (center_of_contr b anot hnot)) == pr1 (pr1 t)).
(*  assert (Hpr1pr1 : pr1 (pr1 (center_of_contr b anot hnot)) == pr1 (pr1 t)).
  simpl.
  set (k1anothnot := (pr2 (pr1 t)) anot hnot).
  set (w := isotoid _ Csat k1anothnot).
  apply w.
*)
  
  
  apply (total2_paths w).
  simpl.
  destruct t as [[c1 k1] q1].
  simpl in *.
  apply funextsec.
  intro a.
  apply funextsec.
  intro h.
  simpl in *.
  set (g := fun (a : precategory_objects A)(h : iso_precat (pr1 H a) b) =>
              (iso_from_fully_faithful_reflection _ _ H Hff _ _  
                  (iso_comp h (iso_inv_from_iso hnot)))).
(*  set (knot := fun (a : precategory_objects A)(h : iso_precat (pr1 H a) b) =>
                    precategory_fun_on_iso _ _ F _ _  (g a h)).
*)
  set (gah := iso_from_fully_faithful_reflection _ _ H Hff _ _ 
                  (iso_comp h (iso_inv_from_iso hnot))).
  set (qhelp := q1 (tpair _ a h)(tpair _ anot hnot) (gah)).
  simpl in *.
  assert (feedtoqhelp : 
        #(pr1 H)
          (fully_faithful_inv_hom A B H Hff a anot (h;; inv_from_iso hnot));;
        hnot == h).
    set (H3 := homotweqinvweq (weq_from_fully_faithful _ _ _ Hff a anot)).
  simpl in H3.
  unfold fully_faithful_inv_hom. simpl.
  rewrite H3.
    rewrite <- precategory_assoc.
    rewrite iso_after_iso_inv.
    apply precategory_id_right.
  set (quack := qhelp feedtoqhelp).
  simpl in *.
  

(*  apply eq_iso_precat. *)
  simpl.
  Check w.
  pathvia (iso_comp  (precategory_fun_on_iso A C F a anot
     (iso_from_fully_faithful_reflection A B H Hff a anot
        (iso_comp h (iso_inv_from_iso hnot)))) (idtoiso w) ).
  generalize w.
  intro w0.
  induction w0.
  simpl.
  rewrite transportf_idpath.
  apply eq_iso_precat. simpl.
  rewrite precategory_id_right.
  apply idpath.
  
  apply eq_iso_precat.
  simpl.
  unfold w.
  rewrite idtoiso_isotoid.
  apply quack.
  
  apply pathsinv0.
  apply (total2_paths Hpr1).
  apply proofirrelevance.
  
  apply impred; intro t0.
  apply impred; intro t'.
  apply impred; intro f.
  apply impred; intro g.
  Check pr2 (pr1 t) (pr1 t0) (pr2 t0).
  apply (pr2 (((pr1 F) (pr1 t0)) --> (pr1 (pr1 t)))).
Qed.
 







End preimage.

End essentially_surjective.

End lemma64.





