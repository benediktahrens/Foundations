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

Let X (b : precategory_objects B) := 
  total2 (fun c : precategory_objects C =>
     total2 (fun k : forall a : precategory_objects A,
                     forall h : iso_precat (pr1 H a) b,
                                iso_precat (pr1 F a) c =>
      forall t t' : total2 (fun a : precategory_objects A => iso_precat (pr1 H a) b),
          forall f : pr1 t --> pr1 t',
             (#(pr1 H) f ;; pr2 t' == pr2 t -> 
                    #(pr1 F) f ;; k (pr1 t') (pr2 t') == k (pr1 t) (pr2 t)))).

Check X.

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
  
  apply h'.
  simpl.
  
  












End preimage.

End essentially_surjective.

End lemma64.





