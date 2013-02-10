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

Notation ob := precategory_objects.
Notation iso := iso_precat.


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


Lemma center_of_contr_proof (b : ob B) (anot : ob A) (hnot : iso ((pr1 H) anot) b) :
  forall (t t' : total2 (fun a : ob A => iso ((pr1 H) a) b))
    (f : pr1 t --> pr1 t'),
  #(pr1 H) f;; pr2 t' == pr2 t ->
  #(pr1 F) f;;
  #(pr1 F) (fully_faithful_inv_hom A B H Hff (pr1 t') anot
     (pr2 t';; inv_from_iso hnot)) ==
  #(pr1 F) (fully_faithful_inv_hom A B H Hff (pr1 t) anot (pr2 t;; inv_from_iso hnot)).
Proof.
  intros t t' f.
  destruct t as [a h].
  destruct t' as [a' h'].
  simpl in *.
  intro star.
  rewrite <- (precategory_fun_comp _ _ F).
  apply maponpaths.
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
Qed.


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
  simpl.
  apply center_of_contr_proof.
Defined.
(*
  apply HH.
 assert (HH : forall (t t' : total2 (fun a : ob A => iso ((pr1 H) a) b))
  (f : pr1 t --> pr1 t'),
#(pr1 H) f;; pr2 t' == pr2 t ->
#(pr1 F) f;;
#F
  (fully_faithful_inv_hom A B H Hff (pr1 t') anot
     (pr2 t';; inv_from_iso hnot)) ==
#F
  (fully_faithful_inv_hom A B H Hff (pr1 t) anot (pr2 t;; inv_from_iso hnot))).

  clear knot. clear g. clear cnot.
  unfold knot.

(*  exists (tpair _ (pr1 F anot) knot). *)
  simpl.
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
  exists (tpair _ (pr1 F anot) knot). 
  apply HH.
Defined.
*)


Lemma claim1_contr_eq (b : ob B) (anot : ob A) (hnot : iso (pr1 H anot) b) : 
   forall t : X b, t == center_of_contr b anot hnot.
Proof.
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
  apply (pr2 (((pr1 F) (pr1 t0)) --> (pr1 (pr1 t)))).
Qed.

(*
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
*)


Definition lemma64_claim1 : forall b : precategory_objects B, iscontr (X b).
Proof.
  intro b.
  assert (HH : isaprop (iscontr (X b))).
  apply isapropiscontr.
  set (pbH := p b (tpair (fun x => isaprop x) (iscontr (X b)) HH)).
  simpl in *.
  apply pbH; clear pbH HH.
  intro t.
  exists (center_of_contr b (pr1 t) (pr2 t)).
  apply (claim1_contr_eq b (pr1 t) (pr2 t)).
Qed.

Definition Go : precategory_objects B -> precategory_objects C :=
   fun b : precategory_objects B =>
      pr1 (pr1 (pr1 (lemma64_claim1 b))).

Let k (b : ob B) : 
     forall a : ob A, iso ((pr1 H) a) b -> iso ((pr1 F) a) (Go b) := 
              pr2 (pr1 (pr1 (lemma64_claim1 b))).

Let q (b : ob B) := pr2 (pr1 (lemma64_claim1 b)).

Check p.

Lemma k_transport (b : ob B) (t : X b) (c : ob C)
   (p' : pr1 (pr1 t) == c) (a : ob A) (h : iso (pr1 H a) b) :
  transportf _ p' (pr2 (pr1 t)) a h == 
         iso_comp (pr2 (pr1 t) a h) (idtoiso p').
Proof.
  destruct t as [[c1 k1] q1]; simpl in *.
  induction p'.
  rewrite transportf_idpath.
  simpl.
  apply eq_iso_precat.
  simpl.
  rewrite precategory_id_right.
  apply idpath.
Qed.


Definition X_contr_base_paths (b : ob B) (t1 t2 : X b) : 
   pr1 (pr1 t1) == pr1 (pr1 t2).
Proof.
  set (e := proofirrelevancecontr (lemma64_claim1 b) t1 t2).
  exact (base_paths _ _ (base_paths _ _ e)).
Defined.

Lemma k_transport_idtoiso (b : ob B) (t1 t2 : X b) 
    (a : ob A) (h : iso (pr1 H a) b) :
  iso_comp (pr2 (pr1 t1) a h) (idtoiso (X_contr_base_paths b t1 t2)) == pr2 (pr1 t2) a h.
Proof.
(*  apply eq_iso_precat. *)
  simpl.
  
  set (e := proofirrelevancecontr (lemma64_claim1 b) t1 t2).
  set (p4 := base_paths _ _ e).
  set (p5 := fiber_path_fibr p4).
  simpl in *.
  rewrite <- p5.
  unfold X_contr_base_paths.
  simpl.
  unfold p4.
  simpl.
  unfold e.
  generalize (base_paths (pr1 t1) (pr1 t2)
        (base_paths t1 t2 (proofirrelevancecontr (lemma64_claim1 b) t1 t2))).
        intro i.
  induction i.
  rewrite transportf_idpath.
  apply eq_iso_precat.
  simpl.
  apply precategory_id_right.
Qed.
 



(*
Lemma k_transport (b : ob B) (*t : X b*) (c : ob C) 
   (p : pr1 (pr1 t) == c) (a : ob A) (h : iso (pr1 H a) b):
transportf (fun c' : ob C => forall a : ob A, iso (pr1 H a) b -> 
                          iso ((pr1 F) a) c')
   p (k) a h == (k b) b a h ;; idtoiso p .
*)


Let Y {b b' : precategory_objects B} (f : b --> b') :=
  total2 (fun g : Go b --> Go b' =>
      forall a : ob A,
        forall h : iso (pr1 H a) b,
          forall a' : ob A,
            forall h' : iso (pr1 H a') b',
              forall l : a --> a',
                #(pr1 H) l ;; h' == h ;; f -> #(pr1 F) l ;; k b' a' h' == k b a h ;; g).

Lemma Y_inhab_proof (b b' : ob B) (f : b --> b') (a0 : ob A) (h0 : iso ((pr1 H) a0) b)
    (a0' : ob A) (h0' : iso ((pr1 H) a0') b') :
  forall (a : ob A) (h : iso ((pr1 H) a) b) (a' : ob A) (h' : iso ((pr1 H) a') b')
    (l : a --> a'),
  #(pr1 H) l;; h' == h;; f ->
  #(pr1 F) l;; k b' a' h' ==
    k b a h;; ((inv_from_iso (k b a0 h0);;
  #(pr1 F) (fully_faithful_inv_hom A B H Hff a0 a0' ((h0;; f);; inv_from_iso h0')));;
       k b' a0' h0').
Proof.
  intros a h a' h' l alpha.
  set (m := iso_from_fully_faithful_reflection _ _ H Hff _ _ 
                  (iso_comp h0 (iso_inv_from_iso h))).
  set (m' := iso_from_fully_faithful_reflection _ _ H Hff _ _ 
                  (iso_comp h0' (iso_inv_from_iso h'))).
  
  assert (sss : iso_comp (precategory_fun_on_iso _ _ F _ _  m) (k b a h) == 
                   k b a0 h0).
  set (qb := q b ). simpl in qb.
  set (qb' := qb (tpair _ a0 h0) (tpair _ a h) m).
  simpl in qb'.
  apply eq_iso_precat; simpl.
  apply qb'. clear qb' qb. 
  set (H3 := homotweqinvweq (weq_from_fully_faithful _ _ _ Hff a0 a)).
  simpl in H3.
  unfold fully_faithful_inv_hom. simpl.
  rewrite H3.
  rewrite <- precategory_assoc.
  rewrite iso_after_iso_inv.
  apply precategory_id_right.
  
  assert (ssss : iso_comp (precategory_fun_on_iso _ _ F _ _  m') (k b' a' h') == 
                   k b' a0' h0').
  set (qb' := q b' (tpair _ a0' h0') (tpair _ a' h') m').
  simpl in qb'.
  apply eq_iso_precat; simpl.
  apply qb'. clear qb'. 
  set (H3 := homotweqinvweq (weq_from_fully_faithful _ _ _ Hff a0' a')).
  simpl in H3.
  unfold fully_faithful_inv_hom. simpl.
  rewrite H3.
  rewrite <- precategory_assoc.
  rewrite iso_after_iso_inv.
  apply precategory_id_right.
  
  set (hfh := h0 ;; f ;; inv_from_iso h0').
  set (l0 := fully_faithful_inv_hom _ _ H Hff _ _ hfh).
  set (g0 := inv_from_iso (k b a0 h0) ;; #(pr1 F) l0  ;; k b' a0' h0').
  
  assert (sssss : #(pr1 H) (l0 ;; m') == #(pr1 H) (m ;; l)).
  rewrite (precategory_fun_comp _ _ H).
  unfold m'. simpl.
  set (H3 := homotweqinvweq (weq_from_fully_faithful _ _ _ Hff a0' a')).
  simpl in H3.
  unfold fully_faithful_inv_hom. simpl.
  rewrite H3. clear H3.
  unfold l0.
  set (H3 := homotweqinvweq (weq_from_fully_faithful _ _ _ Hff a0 a0')).
  simpl in H3.
  unfold fully_faithful_inv_hom. simpl.
  rewrite H3. clear H3.
  
  unfold hfh.
  
  pathvia (h0 ;; f ;; (inv_from_iso h0' ;; h0') ;; inv_from_iso h').
  repeat rewrite precategory_assoc; apply idpath.
  
  rewrite iso_after_iso_inv. rewrite precategory_id_right.
  
  rewrite (precategory_fun_comp _ _ H).
  set (H3 := homotweqinvweq (weq_from_fully_faithful _ _ _ Hff a0 a)).
  simpl in H3.
  unfold fully_faithful_inv_hom. simpl.
  rewrite H3. clear H3.
  repeat rewrite <- precategory_assoc.
  apply maponpaths.
  apply pathsinv0.
  apply iso_inv_on_right.
  rewrite precategory_assoc.
  apply iso_inv_on_left.
  apply pathsinv0.
  apply alpha.

  assert (star5 : inv_from_iso m ;; l0 == l ;; inv_from_iso m').
  apply iso_inv_on_right.
  rewrite precategory_assoc.
  apply iso_inv_on_left.
  apply (equal_transport_along_weq _ _ (weq_from_fully_faithful _ _ _ Hff a0 a' )).
  apply pathsinv0.
  apply sssss.
  
  unfold g0.
  set (sss':= base_paths _ _ sss); simpl in sss'.
  
  assert (sss'' : k b a h ;; inv_from_iso (k b a0 h0) == 
             inv_from_iso (precategory_fun_on_iso _ _ F _ _  m)).
  apply pathsinv0.
  apply iso_inv_on_left.
  apply pathsinv0.
  apply iso_inv_on_right.
  unfold m; simpl.
  apply pathsinv0.
  apply sss'.
  
  repeat rewrite precategory_assoc.
  rewrite sss''. clear sss'' sss' sss.
  
  rewrite <- precategory_fun_on_inv_from_iso.
  rewrite <- (precategory_fun_comp _ _ F).
  rewrite star5. clear star5 sssss.
  
  rewrite precategory_fun_comp.
  rewrite precategory_fun_on_inv_from_iso.
  
  assert (star4 : 
        inv_from_iso (precategory_fun_on_iso A C F a0' a' m');; k b' a0' h0'
           == k b' a' h' ).
  apply iso_inv_on_right.
  set (ssss' := base_paths _ _ ssss).
  apply pathsinv0.
  simpl in ssss'. simpl.
  apply ssss'.
  rewrite <- precategory_assoc.
  rewrite star4.
  apply idpath.
Qed.



Definition Y_inhab (b b' : ob B) (f : b --> b')
      (a0 : ob A) (h0 : iso (pr1 H a0) b) (a0' : ob A) (h0' : iso (pr1 H a0') b') : Y b b' f.
Proof.
  set (hfh := h0 ;; f ;; inv_from_iso h0').
  set (l0 := fully_faithful_inv_hom _ _ H Hff _ _ hfh).
  set (g0 := inv_from_iso (k b a0 h0) ;; #(pr1 F) l0  ;; k b' a0' h0').
  exists g0.
  apply Y_inhab_proof.
Defined.

(*
   apply H456.
  assert (H456 : forall (a : ob A) (h : iso ((pr1 H) a) b) (a' : ob A) 
           (h' : iso ((pr1 H) a') b')
      (l : a --> a'),
         #(pr1 H) l;; h' == h;; f -> #(pr1 F) l;; k b' a' h' == k b a h;; g0).
  unfold g0. clear g0.
  unfold l0; clear l0.
  unfold hfh; clear hfh.
  
  intros a h a' h' l alpha.
  set (m := iso_from_fully_faithful_reflection _ _ H Hff _ _ 
                  (iso_comp h0 (iso_inv_from_iso h))).
  set (m' := iso_from_fully_faithful_reflection _ _ H Hff _ _ 
                  (iso_comp h0' (iso_inv_from_iso h'))).
  
  assert (sss : iso_comp (precategory_fun_on_iso _ _ F _ _  m) (k b a h) == 
                   k b a0 h0).
  set (qb := q b ). simpl in qb.
  set (qb' := qb (tpair _ a0 h0) (tpair _ a h) m).
  simpl in qb'.
  apply eq_iso_precat; simpl.
  apply qb'. clear qb' qb. 
  set (H3 := homotweqinvweq (weq_from_fully_faithful _ _ _ Hff a0 a)).
  simpl in H3.
  unfold fully_faithful_inv_hom. simpl.
  rewrite H3.
  rewrite <- precategory_assoc.
  rewrite iso_after_iso_inv.
  apply precategory_id_right.
  
  assert (ssss : iso_comp (precategory_fun_on_iso _ _ F _ _  m') (k b' a' h') == 
                   k b' a0' h0').
  set (qb' := q b' (tpair _ a0' h0') (tpair _ a' h') m').
  simpl in qb'.
  apply eq_iso_precat; simpl.
  apply qb'. clear qb'. 
  set (H3 := homotweqinvweq (weq_from_fully_faithful _ _ _ Hff a0' a')).
  simpl in H3.
  unfold fully_faithful_inv_hom. simpl.
  rewrite H3.
  rewrite <- precategory_assoc.
  rewrite iso_after_iso_inv.
  apply precategory_id_right.
  
  assert (sssss : #(pr1 H) (l0 ;; m') == #(pr1 H) (m ;; l)).
  rewrite (precategory_fun_comp _ _ H).
  unfold m'. simpl.
  set (H3 := homotweqinvweq (weq_from_fully_faithful _ _ _ Hff a0' a')).
  simpl in H3.
  unfold fully_faithful_inv_hom. simpl.
  rewrite H3. clear H3.
  unfold l0.
  set (H3 := homotweqinvweq (weq_from_fully_faithful _ _ _ Hff a0 a0')).
  simpl in H3.
  unfold fully_faithful_inv_hom. simpl.
  rewrite H3. clear H3.
  
  unfold hfh.
  
  pathvia (h0 ;; f ;; (inv_from_iso h0' ;; h0') ;; inv_from_iso h').
  repeat rewrite precategory_assoc; apply idpath.
  
  rewrite iso_after_iso_inv. rewrite precategory_id_right.
  
  rewrite (precategory_fun_comp _ _ H).
  set (H3 := homotweqinvweq (weq_from_fully_faithful _ _ _ Hff a0 a)).
  simpl in H3.
  unfold fully_faithful_inv_hom. simpl.
  rewrite H3. clear H3.
  repeat rewrite <- precategory_assoc.
  apply maponpaths.
  apply pathsinv0.
  apply iso_inv_on_right.
  rewrite precategory_assoc.
  apply iso_inv_on_left.
  apply pathsinv0.
  apply alpha.

  assert (star5 : inv_from_iso m ;; l0 == l ;; inv_from_iso m').
  apply iso_inv_on_right.
  rewrite precategory_assoc.
  apply iso_inv_on_left.
  apply (equal_transport_along_weq _ _ (weq_from_fully_faithful _ _ _ Hff a0 a' )).
  apply pathsinv0.
  apply sssss.
  
  unfold g0.
  set (sss':= base_paths _ _ sss); simpl in sss'.
  
  assert (sss'' : k b a h ;; inv_from_iso (k b a0 h0) == 
             inv_from_iso (precategory_fun_on_iso _ _ F _ _  m)).
  apply pathsinv0.
  apply iso_inv_on_left.
  apply pathsinv0.
  apply iso_inv_on_right.
  unfold m; simpl.
  apply pathsinv0.
  apply sss'.
  
  repeat rewrite precategory_assoc.
  rewrite sss''. clear sss'' sss' sss.
  
  rewrite <- precategory_fun_on_inv_from_iso.
  rewrite <- (precategory_fun_comp _ _ F).
  rewrite star5. clear star5 sssss.
  
  rewrite precategory_fun_comp.
  rewrite precategory_fun_on_inv_from_iso.
  
  assert (star4 : 
        inv_from_iso (precategory_fun_on_iso A C F a0' a' m');; k b' a0' h0'
           == k b' a' h' ).
  apply iso_inv_on_right.
  set (ssss' := base_paths _ _ ssss).
  apply pathsinv0.
  simpl in ssss'. simpl.
  apply ssss'.
  rewrite <- precategory_assoc.
  rewrite star4.
  apply idpath.
  
   exists g0.
   apply H456.
Defined.
*)

Lemma Y_contr_eq (b b' : ob B) (f : b --> b')
     (a0 : ob A) (h0 : iso (pr1 H a0) b)
     (a0' : ob A) (h0' : iso (pr1 H a0') b') :
  forall t : Y b b' f, t == Y_inhab b b' f a0 h0 a0' h0'.
Proof.
  intro t.
  apply pathsinv0.
  assert (Hpr : pr1 (Y_inhab b b' f a0 h0 a0' h0') == pr1 t).
  destruct t as [g1 r1]; simpl in *.
  rewrite <- precategory_assoc.
  apply iso_inv_on_right.
  set (hfh := h0 ;; f ;; inv_from_iso h0').
  set (l0 := fully_faithful_inv_hom _ _ H Hff _ _ hfh).
  set (r1aioel := r1 a0 h0 a0' h0' l0).
  apply r1aioel.
  unfold l0.
  set (H3 := homotweqinvweq (weq_from_fully_faithful _ _ _ Hff a0 a0')).
  simpl in H3.
  unfold fully_faithful_inv_hom. simpl.
  rewrite H3. clear H3.
  unfold hfh.
  repeat rewrite <- precategory_assoc.
  rewrite iso_after_iso_inv. rewrite precategory_id_right.
  apply idpath.
  apply (total2_paths Hpr).
  apply proofirrelevance.
  apply impred; intro a.
  apply impred; intro h.
  apply impred; intro a'.
  apply impred; intro h'.
  apply impred; intro l.
  apply impred; intro rtu.
  apply (pr2 ((pr1 F) a --> Go b')).
Qed.

Definition Y_iscontr  (b b' : ob B) (f : b --> b') : 
   iscontr (Y b b' f).
Proof.
  assert (HH : isaprop (iscontr (Y b b' f))).
  apply isapropiscontr.
  set (pbH := p b (tpair (fun x => isaprop x) (iscontr (Y b b' f)) HH)).
  simpl in *.
  apply pbH; clear pbH.
  intros [a0 h0].
  set (pbH := p b' (tpair (fun x => isaprop x) (iscontr (Y b b' f)) HH)).
  simpl in *.
  apply pbH; clear pbH.
  intros [a0' h0'].
  clear HH.
  
  exists (Y_inhab b b' f a0 h0 a0' h0').
  apply Y_contr_eq.
Qed.


Definition G_precategory_ob_mor_fun : precategory_ob_mor_fun B C.
Proof.
  exists Go.
  intros b b' f.
  exact (pr1 (pr1 (Y_iscontr b b' f))).
Defined.


Notation "'G' f" := (pr1 (pr1 (Y_iscontr _ _ f))) (at level 3).


Lemma is_precategory_fun : is_precategory_fun G_precategory_ob_mor_fun.
Proof.
  split; simpl.
  intro b.
  
  assert (PR2 : forall (a : ob A) (h : iso ((pr1 H) a) b) (a' : ob A) 
          (h' : iso ((pr1 H) a') b)
    (l : a --> a'),
  #(pr1 H) l;; h' == h;; precategory_identity b ->
  #(pr1 F) l;; k b a' h' == k b a h;; precategory_identity (Go b)).
  intros a h a' h' l LL.
  rewrite precategory_id_right.
  set (qb := q b (tpair _ a h) (tpair _ a' h') l).
  simpl in qb.
  apply qb.
  rewrite precategory_id_right in LL.
  apply LL.
  set (Gbrtilde :=
           tpair _ (precategory_identity (Go b)) PR2 : Y b b (precategory_identity b)).
(*   (Gbrtilde : Y b b (precategory_identity b)).
  exists (precategory_identity (Go b)).
    
  intros a h a' h' l LL.
  rewrite precategory_id_right.
  set (qb := q b (tpair _ a h) (tpair _ a' h') l).
  simpl in qb.
  apply qb.
  rewrite precategory_id_right in LL.
  apply LL.
*)
  
  set (H' := pr2 (Y_iscontr b b (precategory_identity b)) Gbrtilde).
  set (H'' := base_paths _ _ H').
  simpl in H'.
  rewrite <- H'.
  apply idpath.
  
  
  (** composition *)

  intros b b' b'' f f'.

  assert (HHHH : isaprop (pr1 (pr1 (Y_iscontr b b'' (f;; f'))) ==
                        pr1 (pr1 (Y_iscontr b b' f));; pr1 (pr1 (Y_iscontr b' b'' f')))).
  apply (pr2 (Go b --> Go b'')).
  apply (p b (tpair (fun x => isaprop x) (pr1 (pr1 (Y_iscontr b b'' (f;; f'))) ==
           pr1 (pr1 (Y_iscontr b b' f));; pr1 (pr1 (Y_iscontr b' b'' f'))) HHHH)).
  intros [a0 h0].
  simpl.
  apply (p b' (tpair (fun x => isaprop x) (pr1 (pr1 (Y_iscontr b b'' (f;; f'))) ==
           pr1 (pr1 (Y_iscontr b b' f));; pr1 (pr1 (Y_iscontr b' b'' f'))) HHHH)).
  intros [a0' h0'].
  simpl.
  apply (p b'' (tpair (fun x => isaprop x) (pr1 (pr1 (Y_iscontr b b'' (f;; f'))) ==
           pr1 (pr1 (Y_iscontr b b' f));; pr1 (pr1 (Y_iscontr b' b'' f'))) HHHH)).
  intros [a0'' h0''].
  simpl; clear HHHH.

(*  
  set (hfh := h0 ;; f ;; inv_from_iso h0').
  set (l0 := fully_faithful_inv_hom _ _ H Hff _ _ hfh).
*)
  set (l0 := fully_faithful_inv_hom A B H Hff _ _ (h0 ;; f ;; inv_from_iso h0')).
  set (l0' := fully_faithful_inv_hom A B H Hff _ _ (h0' ;; f' ;; inv_from_iso h0'')).
  set (l0'' := fully_faithful_inv_hom A B H Hff _ _ (h0 ;; (f;; f') ;; inv_from_iso h0'')).

  
  assert (L : l0 ;; l0' == l0'').
  apply (equal_transport_along_weq _ _ (weq_from_fully_faithful _ _ _ Hff a0 a0'')).
  simpl.
  rewrite precategory_fun_comp.
  unfold l0'.
  set (HFFaa := homotweqinvweq (weq_from_fully_faithful A B H Hff a0' a0'')).
  unfold fully_faithful_inv_hom.
  simpl in *.
  rewrite HFFaa.
  clear HFFaa.
  
  unfold l0.
  set (HFFaa := homotweqinvweq (weq_from_fully_faithful A B H Hff a0 a0')).
  unfold fully_faithful_inv_hom.
  simpl in *.
  rewrite HFFaa.
  clear HFFaa.
  pathvia (h0 ;; f ;; (inv_from_iso h0' ;; h0') ;; f' ;; inv_from_iso h0'').
  repeat rewrite precategory_assoc; apply idpath.
  rewrite iso_after_iso_inv. rewrite precategory_id_right.
  unfold l0''.
  set (HFFaa := homotweqinvweq (weq_from_fully_faithful A B H Hff a0 a0'')).
  unfold fully_faithful_inv_hom.
  simpl in *.
  rewrite HFFaa.
  clear HFFaa.
  repeat rewrite precategory_assoc; apply idpath.
  
  
  assert (PR2 : forall (a : ob A) (h : iso ((pr1 H) a) b)(a' : ob A)
          (h' : iso ((pr1 H) a') b')
            (l : a --> a'),
           #(pr1 H) l;; h' == h;; f ->
           #(pr1 F) l;; k b' a' h' ==
            k b a h;; ((inv_from_iso (k b a0 h0);; #(pr1 F) l0);; k b' a0' h0') ).
  
  intros a h a' h' l.
  intro alpha.
  set (m := iso_from_fully_faithful_reflection _ _ H Hff _ _ 
                  (iso_comp h0 (iso_inv_from_iso h))).
  set (m' := iso_from_fully_faithful_reflection _ _ H Hff _ _ 
                  (iso_comp h0' (iso_inv_from_iso h'))).
  
  assert (sss : iso_comp (precategory_fun_on_iso _ _ F _ _  m) (k b a h) == 
                   k b a0 h0).
  set (qb := q b ). simpl in qb.
  set (qb' := qb (tpair _ a0 h0) (tpair _ a h) m).
  simpl in qb'.
  apply eq_iso_precat; simpl.
  apply qb'. clear qb' qb. 
  set (H3 := homotweqinvweq (weq_from_fully_faithful _ _ _ Hff a0 a)).
  simpl in H3.
  unfold fully_faithful_inv_hom. simpl.
  rewrite H3.
  rewrite <- precategory_assoc.
  rewrite iso_after_iso_inv.
  apply precategory_id_right.
  
  assert (ssss : iso_comp (precategory_fun_on_iso _ _ F _ _  m') (k b' a' h') == 
                   k b' a0' h0').
  set (qb' := q b' (tpair _ a0' h0') (tpair _ a' h') m').
  simpl in qb'.
  apply eq_iso_precat; simpl.
  apply qb'. clear qb'. 
  set (H3 := homotweqinvweq (weq_from_fully_faithful _ _ _ Hff a0' a')).
  simpl in H3.
  unfold fully_faithful_inv_hom. simpl.
  rewrite H3.
  rewrite <- precategory_assoc.
  rewrite iso_after_iso_inv.
  apply precategory_id_right.
  
  assert (sssss : #(pr1 H) (l0 ;; m') == #(pr1 H) (m ;; l)).
  rewrite (precategory_fun_comp _ _ H).
  unfold m'. simpl.
  set (H3 := homotweqinvweq (weq_from_fully_faithful _ _ _ Hff a0' a')).
  simpl in H3.
  unfold fully_faithful_inv_hom. simpl.
  rewrite H3. clear H3.
  unfold l0.
  set (H3 := homotweqinvweq (weq_from_fully_faithful _ _ _ Hff a0 a0')).
  simpl in H3.
  unfold fully_faithful_inv_hom. simpl.
  rewrite H3. clear H3.
  
(*  unfold hfh.*)
  
  pathvia (h0 ;; f ;; (inv_from_iso h0' ;; h0') ;; inv_from_iso h').
  repeat rewrite precategory_assoc; apply idpath.
  
  rewrite iso_after_iso_inv. rewrite precategory_id_right.
  
  rewrite (precategory_fun_comp _ _ H).
  set (H3 := homotweqinvweq (weq_from_fully_faithful _ _ _ Hff a0 a)).
  simpl in H3.
  unfold fully_faithful_inv_hom. simpl.
  rewrite H3. clear H3.
  repeat rewrite <- precategory_assoc.
  apply maponpaths.
  apply pathsinv0.
  apply iso_inv_on_right.
  rewrite precategory_assoc.
  apply iso_inv_on_left.
  apply pathsinv0.
  apply alpha.

  assert (star5 : inv_from_iso m ;; l0 == l ;; inv_from_iso m').
  apply iso_inv_on_right.
  rewrite precategory_assoc.
  apply iso_inv_on_left.
  apply (equal_transport_along_weq _ _ (weq_from_fully_faithful _ _ _ Hff a0 a' )).
  apply pathsinv0.
  apply sssss.
  
(*  unfold g0. *)
  set (sss':= base_paths _ _ sss); simpl in sss'.
  
  assert (sss'' : k b a h ;; inv_from_iso (k b a0 h0) == 
             inv_from_iso (precategory_fun_on_iso _ _ F _ _  m)).
  apply pathsinv0.
  apply iso_inv_on_left.
  apply pathsinv0.
  apply iso_inv_on_right.
  unfold m; simpl.
  apply pathsinv0.
  apply sss'.
  
  repeat rewrite precategory_assoc.
  rewrite sss''. clear sss'' sss' sss.
  
  rewrite <- precategory_fun_on_inv_from_iso.
  rewrite <- (precategory_fun_comp _ _ F).
  rewrite star5. clear star5 sssss.
  
  rewrite precategory_fun_comp.
  rewrite precategory_fun_on_inv_from_iso.
  
  assert (star4 : 
        inv_from_iso (precategory_fun_on_iso A C F a0' a' m');; k b' a0' h0'
           == k b' a' h' ).
  apply iso_inv_on_right.
  set (ssss' := base_paths _ _ ssss).
  apply pathsinv0.
  simpl in ssss'. simpl.
  apply ssss'.
  rewrite <- precategory_assoc.
  rewrite star4.
  apply idpath.
  
  assert (HGf : G f == inv_from_iso (k b a0 h0) ;; #(pr1 F) l0 ;; k b' a0' h0'). 
  
  set (Gbrtilde :=
           tpair _ (inv_from_iso (k b a0 h0) ;; #(pr1 F) l0 ;; k b' a0' h0') PR2 : Y b b' f).
  
  set (H' := pr2 (Y_iscontr b b' f) Gbrtilde).
  set (H'' := base_paths _ _ H').
  simpl in H'.
  rewrite <- H'.
  apply idpath.
  
  clear PR2.
(*  
  assert (Test : Y b' b'' f').
  exists (inv_from_iso (k b' a0' h0') ;; #(pr1 F) l0' ;; k b'' a0'' h0'').
*)  
  assert (PR2 : forall (a : ob A) (h : iso ((pr1 H) a) b') (a' : ob A) 
            (h' : iso ((pr1 H) a') b'')
                (l : a --> a'),
         #(pr1 H) l;; h' == h;; f' ->
           #(pr1 F) l;; k b'' a' h' ==
         k b' a h;; ((inv_from_iso (k b' a0' h0');; #(pr1 F) l0');; k b'' a0'' h0'')).
  
  intros a' h' a'' h'' l'.
  intro alpha.
  set (m := iso_from_fully_faithful_reflection _ _ H Hff _ _ 
                  (iso_comp h0' (iso_inv_from_iso h'))).
  set (m' := iso_from_fully_faithful_reflection _ _ H Hff _ _ 
                  (iso_comp h0'' (iso_inv_from_iso h''))).
  
  assert (sss : iso_comp (precategory_fun_on_iso _ _ F _ _  m) (k b' a' h') == 
                   k b' a0' h0').
  set (qb := q b' ). simpl in qb.
  set (qb' := qb (tpair _ a0' h0') (tpair _ a' h') m).
  simpl in qb'.
  apply eq_iso_precat; simpl.
  apply qb'. clear qb' qb. 
  set (H3 := homotweqinvweq (weq_from_fully_faithful _ _ _ Hff a0' a')).
  simpl in H3.
  unfold fully_faithful_inv_hom. simpl.
  rewrite H3.
  rewrite <- precategory_assoc.
  rewrite iso_after_iso_inv.
  apply precategory_id_right.
  
  assert (ssss : iso_comp (precategory_fun_on_iso _ _ F _ _  m') (k b'' a'' h'') == 
                   k b'' a0'' h0'').
  set (qb' := q b'' (tpair _ a0'' h0'') (tpair _ a'' h'') m').
  simpl in qb'.
  apply eq_iso_precat; simpl.
  apply qb'. clear qb'. 
  set (H3 := homotweqinvweq (weq_from_fully_faithful _ _ _ Hff a0'' a'')).
  simpl in H3.
  unfold fully_faithful_inv_hom. simpl.
  rewrite H3.
  rewrite <- precategory_assoc.
  rewrite iso_after_iso_inv.
  apply precategory_id_right.
  
  assert (sssss : #(pr1 H) (l0' ;; m') == #(pr1 H) (m ;; l')).
  rewrite (precategory_fun_comp _ _ H).
  unfold m'. simpl.
  set (H3 := homotweqinvweq (weq_from_fully_faithful _ _ _ Hff a0'' a'')).
  simpl in H3.
  unfold fully_faithful_inv_hom. simpl.
  rewrite H3. clear H3.
  unfold l0'.
  set (H3 := homotweqinvweq (weq_from_fully_faithful _ _ _ Hff a0' a0'')).
  simpl in H3.
  unfold fully_faithful_inv_hom. simpl.
  rewrite H3. clear H3.
  
(*  unfold hfh.*)
  
  pathvia (h0' ;; f' ;; (inv_from_iso h0'' ;; h0'') ;; inv_from_iso h'').
  repeat rewrite precategory_assoc; apply idpath.
  
  rewrite iso_after_iso_inv. rewrite precategory_id_right.
  
  rewrite (precategory_fun_comp _ _ H).
  set (H3 := homotweqinvweq (weq_from_fully_faithful _ _ _ Hff a0' a')).
  simpl in H3.
  unfold fully_faithful_inv_hom. simpl.
  rewrite H3. clear H3.
  repeat rewrite <- precategory_assoc.
  apply maponpaths.
  apply pathsinv0.
  apply iso_inv_on_right.
  rewrite precategory_assoc.
  apply iso_inv_on_left.
  apply pathsinv0.
  apply alpha.

  assert (star5 : inv_from_iso m ;; l0' == l' ;; inv_from_iso m').
  apply iso_inv_on_right.
  rewrite precategory_assoc.
  apply iso_inv_on_left.
  apply (equal_transport_along_weq _ _ (weq_from_fully_faithful _ _ _ Hff a0' a'' )).
  apply pathsinv0.
  apply sssss.
  
(*  unfold g0. *)
  set (sss':= base_paths _ _ sss); simpl in sss'.
  
  assert (sss'' : k b' a' h' ;; inv_from_iso (k b' a0' h0') == 
             inv_from_iso (precategory_fun_on_iso _ _ F _ _  m)).
  apply pathsinv0.
  apply iso_inv_on_left.
  apply pathsinv0.
  apply iso_inv_on_right.
  unfold m; simpl.
  apply pathsinv0.
  apply sss'.
  
  repeat rewrite precategory_assoc.
  rewrite sss''. clear sss'' sss' sss.
  
  rewrite <- precategory_fun_on_inv_from_iso.
  rewrite <- (precategory_fun_comp _ _ F).
  rewrite star5. clear star5 sssss.
  
  rewrite precategory_fun_comp.
  rewrite precategory_fun_on_inv_from_iso.
  
  assert (star4 : 
        inv_from_iso (precategory_fun_on_iso A C F a0'' a'' m');; k b'' a0'' h0''
           == k b'' a'' h'' ).
  apply iso_inv_on_right.
  set (ssss' := base_paths _ _ ssss).
  apply pathsinv0.
  simpl in ssss'. simpl.
  apply ssss'.
  rewrite <- precategory_assoc.
  rewrite star4.
  apply idpath.
  
  assert (HGf' : G f' == inv_from_iso (k b' a0' h0') ;; #(pr1 F) l0' ;; k b'' a0'' h0''). 
  
  set (Gbrtilde :=
       tpair _ (inv_from_iso (k b' a0' h0') ;; #(pr1 F) l0' ;; k b'' a0'' h0'') PR2 : 
                      Y b' b'' f').
  
  set (H' := pr2 (Y_iscontr b' b'' f') Gbrtilde).
  set (H'' := base_paths _ _ H').
  simpl in H'.
  rewrite <- H'.
  apply idpath.
  
  clear PR2.
(*  
  assert (Test : Y b b'' (f;;f')).
  exists (inv_from_iso (k b a0 h0) ;; #(pr1 F) l0'' ;; k b'' a0'' h0'').
*)  
  assert (PR2 : forall (a : ob A) (h : iso ((pr1 H) a) b) (a' : ob A) 
             (h' : iso ((pr1 H) a') b'')
                (l : a --> a'),
          #(pr1 H) l;; h' == h;; (f;; f') ->
          #(pr1 F) l;; k b'' a' h' ==
           k b a h;; ((inv_from_iso (k b a0 h0);; #(pr1 F) l0'');; k b'' a0'' h0'')).
  

  intros a h a'' h'' l.
  intro alpha.
  set (m := iso_from_fully_faithful_reflection _ _ H Hff _ _ 
                  (iso_comp h0 (iso_inv_from_iso h))).
  set (m' := iso_from_fully_faithful_reflection _ _ H Hff _ _ 
                  (iso_comp h0'' (iso_inv_from_iso h''))).
  
  assert (sss : iso_comp (precategory_fun_on_iso _ _ F _ _  m) (k b a h) == 
                   k b a0 h0).
  set (qb := q b ). simpl in qb.
  set (qb' := qb (tpair _ a0 h0) (tpair _ a h) m).
  simpl in qb'.
  apply eq_iso_precat; simpl.
  apply qb'. clear qb' qb. 
  set (H3 := homotweqinvweq (weq_from_fully_faithful _ _ _ Hff a0 a)).
  simpl in H3.
  unfold fully_faithful_inv_hom. simpl.
  rewrite H3.
  rewrite <- precategory_assoc.
  rewrite iso_after_iso_inv.
  apply precategory_id_right.
  
  assert (ssss : iso_comp (precategory_fun_on_iso _ _ F _ _  m') (k b'' a'' h'') == 
                   k b'' a0'' h0'').
  set (qb' := q b'' (tpair _ a0'' h0'') (tpair _ a'' h'') m').
  simpl in qb'.
  apply eq_iso_precat; simpl.
  apply qb'. clear qb'. 
  set (H3 := homotweqinvweq (weq_from_fully_faithful _ _ _ Hff a0'' a'')).
  simpl in H3.
  unfold fully_faithful_inv_hom. simpl.
  rewrite H3.
  rewrite <- precategory_assoc.
  rewrite iso_after_iso_inv.
  apply precategory_id_right.
  
  assert (sssss : #(pr1 H) (l0'' ;; m') == #(pr1 H) (m ;; l)).
  rewrite (precategory_fun_comp _ _ H).
  unfold m'. simpl.
  set (H3 := homotweqinvweq (weq_from_fully_faithful _ _ _ Hff a0'' a'')).
  simpl in H3.
  unfold fully_faithful_inv_hom. simpl.
  rewrite H3. clear H3.
  unfold l0''.
  set (H3 := homotweqinvweq (weq_from_fully_faithful _ _ _ Hff a0 a0'')).
  simpl in H3.
  unfold fully_faithful_inv_hom. simpl.
  rewrite H3. clear H3.
  
(*  unfold hfh.*)
  
  pathvia (h0 ;; (f ;; f') ;; (inv_from_iso h0'' ;; h0'') ;; inv_from_iso h'').
  repeat rewrite precategory_assoc; apply idpath.
  
  rewrite iso_after_iso_inv. rewrite precategory_id_right.
  
  rewrite (precategory_fun_comp _ _ H).
  set (H3 := homotweqinvweq (weq_from_fully_faithful _ _ _ Hff a0 a)).
  simpl in H3.
  unfold fully_faithful_inv_hom. simpl.
  rewrite H3. clear H3.
  repeat rewrite <- precategory_assoc.
  apply maponpaths.
  apply pathsinv0.
  apply iso_inv_on_right.
  repeat rewrite precategory_assoc.
  apply iso_inv_on_left.
  apply pathsinv0.
  repeat rewrite <- precategory_assoc.
  apply alpha.

  assert (star5 : inv_from_iso m ;; l0'' == l ;; inv_from_iso m').
  apply iso_inv_on_right.
  rewrite precategory_assoc.
  apply iso_inv_on_left.

  apply (equal_transport_along_weq _ _ (weq_from_fully_faithful _ _ _ Hff a0 a'' )).
  apply pathsinv0.
  apply sssss.
  
(*  unfold g0. *)
  set (sss':= base_paths _ _ sss); simpl in sss'.
  
  assert (sss'' : k b a h ;; inv_from_iso (k b a0 h0) == 
             inv_from_iso (precategory_fun_on_iso _ _ F _ _  m)).
  apply pathsinv0.
  apply iso_inv_on_left.
  apply pathsinv0.
  apply iso_inv_on_right.
  unfold m; simpl.
  apply pathsinv0.
  apply sss'.
  
  repeat rewrite precategory_assoc.
  rewrite sss''. clear sss'' sss' sss.
  
  rewrite <- precategory_fun_on_inv_from_iso.
  rewrite <- (precategory_fun_comp _ _ F).
  rewrite star5. clear star5 sssss.
  
  rewrite precategory_fun_comp.
  rewrite precategory_fun_on_inv_from_iso.
  
  assert (star4 : 
        inv_from_iso (precategory_fun_on_iso A C F a0'' a'' m');; k b'' a0'' h0''
           == k b'' a'' h'' ).
  apply iso_inv_on_right.
  set (ssss' := base_paths _ _ ssss).
  apply pathsinv0.
  simpl in ssss'. simpl.
  apply ssss'.
  rewrite <- precategory_assoc.
  rewrite star4.
  apply idpath.

  assert (HGff' : G (f ;; f') == 
       inv_from_iso (k b a0 h0) ;; #(pr1 F) l0'' ;; k b'' a0'' h0''). 
  
  set (Gbrtilde :=
           tpair _ (inv_from_iso (k b a0 h0) ;; #(pr1 F) l0'' ;; k b'' a0'' h0'') PR2 : 
               Y b b'' (f ;; f')).
  
  set (H' := pr2 (Y_iscontr b b'' (f ;; f')) Gbrtilde).
  set (H'' := base_paths _ _ H').
  simpl in H'.
  rewrite <- H'.
  apply idpath.
  clear PR2.
  
  rewrite HGf.
  rewrite HGf'.
  
  pathvia (inv_from_iso (k b a0 h0);; #(pr1 F) l0;; (k b' a0' h0';;
              inv_from_iso (k b' a0' h0'));; #(pr1 F) l0';; k b'' a0'' h0'').
              
  rewrite iso_inv_after_iso; rewrite precategory_id_right.
  
  rewrite HGff'. 
  repeat rewrite <- precategory_assoc.
  apply maponpaths.
  rewrite <- L.
  rewrite (precategory_fun_comp _ _ F).
  repeat rewrite <- precategory_assoc.
  apply idpath.
  
  repeat rewrite <- precategory_assoc.
  
  apply idpath.

Qed.

Definition GG : ob [B, C] := tpair _ G_precategory_ob_mor_fun is_precategory_fun.

Lemma santas_little_helper (a0 : ob A) :
  forall (t t' : total2 (fun a : ob A => iso ((pr1 H) a) ((pr1 H) a0)))
    (f : pr1 t --> pr1 t'),
  #(pr1 H) f;; pr2 t' == pr2 t ->
  #(pr1 F) f;; #(pr1 F) (fully_faithful_inv_hom A B H Hff (pr1 t') a0 (pr2 t')) ==
  #(pr1 F) (fully_faithful_inv_hom A B H Hff (pr1 t) a0 (pr2 t)).
Proof.
  simpl.
  intros [a h] [a' h'] f L.
  simpl in L; simpl.
(*
  set (HHH := precategory_fun_comp A C F _ _ _ f (fully_faithful_inv_hom A B H Hff a' a0 h')).
  simpl in HHH.
  rewrite <- HHH.
  elim HHH.
*)
  rewrite <- (precategory_fun_comp A C F).
  apply maponpaths.
  set (hhh':=equal_transport_along_weq _ _ (weq_from_fully_faithful A B H Hff a a0)
                 (f;; fully_faithful_inv_hom A B H Hff a' a0 h')                      
                 (fully_faithful_inv_hom A B H Hff a a0 h)  ).
  simpl in *.
  apply hhh'. clear hhh'.
  set (HFFaa := homotweqinvweq (weq_from_fully_faithful _ _ H Hff a a0)).
  unfold fully_faithful_inv_hom.
  simpl in *.
  rewrite HFFaa. clear HFFaa.
  rewrite precategory_fun_comp.
  set (HFFaa := homotweqinvweq (weq_from_fully_faithful _ _ H Hff a' a0)).
  unfold fully_faithful_inv_hom.
  simpl in *.
  rewrite HFFaa. clear HFFaa.
  apply L.
Qed.

Lemma phi (a0 : ob A) : pr1 (pr1 (GG O H)) a0 == pr1 (pr1 F) a0.
Proof.
 set (kFa := fun (a : ob A) (h : iso (pr1 H a) (pr1 H a0)) =>
                precategory_fun_on_iso A C F _ _ 
                  (iso_from_fully_faithful_reflection _ _ H Hff _ _ h)).
(*
  assert (HYpr2 : forall (t t' : total2 (fun a : ob A => iso ((pr1 H) a) ((pr1 H) a0)))
         (f : pr1 t --> pr1 t'),
              #(pr1 H) f;; pr2 t' == pr2 t ->
     #(pr1 F) f;; #(pr1 F) (fully_faithful_inv_hom A B H Hff (pr1 t') a0 (pr2 t')) ==
         #(pr1 F) (fully_faithful_inv_hom A B H Hff (pr1 t) a0 (pr2 t))).
  clear kFa.
(*  
*)
  simpl.
  intros [a h] [a' h'] f L.
  simpl in L; simpl.
(*
  set (HHH := precategory_fun_comp A C F _ _ _ f (fully_faithful_inv_hom A B H Hff a' a0 h')).
  simpl in HHH.
  rewrite <- HHH.
  elim HHH.
*)
  rewrite <- (precategory_fun_comp A C F).
  apply maponpaths.
  set (hhh':=equal_transport_along_weq _ _ (weq_from_fully_faithful A B H Hff a a0)
                 (f;; fully_faithful_inv_hom A B H Hff a' a0 h')                      
                 (fully_faithful_inv_hom A B H Hff a a0 h)  ).
  simpl in *.
  apply hhh'. clear hhh'.
  set (HFFaa := homotweqinvweq (weq_from_fully_faithful _ _ H Hff a a0)).
  unfold fully_faithful_inv_hom.
  simpl in *.
  rewrite HFFaa. clear HFFaa.
  rewrite precategory_fun_comp.
  set (HFFaa := homotweqinvweq (weq_from_fully_faithful _ _ H Hff a' a0)).
  unfold fully_faithful_inv_hom.
  simpl in *.
  rewrite HFFaa. clear HFFaa.
  apply L.
*) 
  set (HYpr1 :=  (tpair (fun c : precategory_objects C =>
                forall a : precategory_objects A,
                     iso_precat (pr1 H a) (pr1 H a0) -> 
      iso_precat (pr1 F a) c) (pr1 F a0) kFa)).
  set (HY := tpair (fun ck : 
  total2 (fun c : precategory_objects C =>
                forall a : precategory_objects A,
                     iso_precat (pr1 H a) (pr1 H a0) -> iso_precat (pr1 F a) c) =>
    forall t t' : total2 (fun a : precategory_objects A => iso_precat (pr1 H a) (pr1 H a0)),
          forall f : pr1 t --> pr1 t',
             (#(pr1 H) f ;; pr2 t' == pr2 t -> 
                    #(pr1 F) f ;; pr2 ck (pr1 t') (pr2 t') == pr2 ck (pr1 t) (pr2 t)))  
       (HYpr1) (santas_little_helper a0) : X (pr1 H a0)).
  
  set (hula := pr2 (lemma64_claim1 (pr1 H a0)) HY ).
  set (hulapr2 := base_paths _ _ (base_paths _ _ hula)).
  simpl in hulapr2.
(*  apply pathsinv0. *)
  apply (!hulapr2).
(*  change (pr1 (pr1 F) a0) with (pr1 F a0).
  clearbody hulapr2.
  set (h5 := ! hulapr2).
  clearbody h5.
  induction h5.
  
(*  induction (! hulapr2). *)
  apply idpath.
*)
Qed.


Lemma extphi : pr1 (pr1 (GG O H)) == pr1 (pr1 F).
Proof.
  apply funextsec.
  apply phi.
Defined.
(*
  set (kFa := fun (a : ob A) (h : iso (pr1 H a) (pr1 H a0)) =>
                precategory_fun_on_iso A C F _ _ 
                  (iso_from_fully_faithful_reflection _ _ H Hff _ _ h)).
(*
  assert (HYpr2 : forall (t t' : total2 (fun a : ob A => iso ((pr1 H) a) ((pr1 H) a0)))
         (f : pr1 t --> pr1 t'),
              #(pr1 H) f;; pr2 t' == pr2 t ->
     #(pr1 F) f;; #(pr1 F) (fully_faithful_inv_hom A B H Hff (pr1 t') a0 (pr2 t')) ==
         #(pr1 F) (fully_faithful_inv_hom A B H Hff (pr1 t) a0 (pr2 t))).
  clear kFa.
(*  
*)
  simpl.
  intros [a h] [a' h'] f L.
  simpl in L; simpl.
(*
  set (HHH := precategory_fun_comp A C F _ _ _ f (fully_faithful_inv_hom A B H Hff a' a0 h')).
  simpl in HHH.
  rewrite <- HHH.
  elim HHH.
*)
  rewrite <- (precategory_fun_comp A C F).
  apply maponpaths.
  set (hhh':=equal_transport_along_weq _ _ (weq_from_fully_faithful A B H Hff a a0)
                 (f;; fully_faithful_inv_hom A B H Hff a' a0 h')                      
                 (fully_faithful_inv_hom A B H Hff a a0 h)  ).
  simpl in *.
  apply hhh'. clear hhh'.
  set (HFFaa := homotweqinvweq (weq_from_fully_faithful _ _ H Hff a a0)).
  unfold fully_faithful_inv_hom.
  simpl in *.
  rewrite HFFaa. clear HFFaa.
  rewrite precategory_fun_comp.
  set (HFFaa := homotweqinvweq (weq_from_fully_faithful _ _ H Hff a' a0)).
  unfold fully_faithful_inv_hom.
  simpl in *.
  rewrite HFFaa. clear HFFaa.
  apply L.
*) 
  set (HYpr1 :=  (tpair (fun c : precategory_objects C =>
                forall a : precategory_objects A,
                     iso_precat (pr1 H a) (pr1 H a0) -> 
      iso_precat (pr1 F a) c) (pr1 F a0) kFa)).
                     Check tpair.
  set (HY := tpair (fun ck : 
  total2 (fun c : precategory_objects C =>
                forall a : precategory_objects A,
                     iso_precat (pr1 H a) (pr1 H a0) -> iso_precat (pr1 F a) c) =>
    forall t t' : total2 (fun a : precategory_objects A => iso_precat (pr1 H a) (pr1 H a0)),
          forall f : pr1 t --> pr1 t',
             (#(pr1 H) f ;; pr2 t' == pr2 t -> 
                    #(pr1 F) f ;; pr2 ck (pr1 t') (pr2 t') == pr2 ck (pr1 t) (pr2 t)))  
       (HYpr1) (santas_little_helper a0) : X (pr1 H a0)).
  
  set (hula := pr2 (lemma64_claim1 (pr1 H a0)) HY ).
  set (hulapr2 := base_paths _ _ (base_paths _ _ hula)).
  simpl in hulapr2.
(*  apply pathsinv0. *)

  change (pr1 (pr1 F) a0) with (pr1 F a0).
  clearbody hulapr2.
  set (h5 := ! hulapr2).
  clearbody h5.
  induction h5.
  
(*  induction (! hulapr2). *)
  apply idpath.
Defined.
*)

Lemma bla : GG O H == F.
Proof.
  apply (precategory_fun_eq _ _ (GG O H) F).
  apply (total2_paths extphi).
  apply funextsec. intro a0.
  apply funextsec. intro a0'.
  apply funextsec. intro f.
  
(*
  apply (transport_to_the_right _ (fun x : ob A -> ob C => 
               forall a b : ob A, a --> b -> x a --> x b)).
  *)           
  
  
  
  rewrite weird_lemma.
  unfold extphi.
  rewrite toforallpaths_funextsec.
  rewrite <- idtoiso_postcompose.
  rewrite <- idtoiso_precompose.
  
  rewrite idtoiso_inv.
  
  
  (* ***** STOPPED HERE   *)
  
  unfold pr1pr1functor.
  rewrite toforallpaths_funextsec.
  simpl.
  
  generalize ((identity_rect (pr1 (pr1 (pr1 (lemma64_claim1 ((pr1 H) b)))))
     (fun (y : ob C) (_ : pr1 (pr1 (pr1 (lemma64_claim1 ((pr1 H) b)))) == y) =>
      y == pr1 (pr1 (pr1 (lemma64_claim1 ((pr1 H) b)))) -> Go (pr1 H b) == y)
     (fun
        _ : pr1 (pr1 (pr1 (lemma64_claim1 ((pr1 H) b)))) ==
            pr1 (pr1 (pr1 (lemma64_claim1 ((pr1 H) b)))) =>
      idpath (pr1 (pr1 (pr1 (lemma64_claim1 ((pr1 H) b)))))) ((pr1 F) b)
     (!base_paths
         {|
         pr1 := (pr1 F) b;
         pr2 := fun (a0 : A) (h : iso ((pr1 H) a0) ((pr1 H) b)) =>
                precategory_fun_on_iso A C F a0 b
                  (iso_from_fully_faithful_reflection A B H Hff a0 b h) |}
         (pr1 (pr1 (lemma64_claim1 ((pr1 H) b))))
         (base_paths
            {|
            pr1 := {|
                   pr1 := (pr1 F) b;
                   pr2 := fun (a0 : A) (h : iso ((pr1 H) a0) ((pr1 H) b)) =>
                          precategory_fun_on_iso A C F a0 b
                            (iso_from_fully_faithful_reflection A B H Hff a0
                               b h) |};
            pr2 := santas_little_helper b |}
            (pr1 (lemma64_claim1 ((pr1 H) b)))
            (pr2 (lemma64_claim1 ((pr1 H) b))
               {|
               pr1 := {|
                      pr1 := (pr1 F) b;
                      pr2 := fun (a0 : A) (h : iso ((pr1 H) a0) ((pr1 H) b)) =>
                             precategory_fun_on_iso A C F a0 b
                               (iso_from_fully_faithful_reflection A B H Hff
                                  a0 b h) |};
               pr2 := santas_little_helper b |})))
     (base_paths
        {|
        pr1 := (pr1 F) b;
        pr2 := fun (a0 : A) (h : iso ((pr1 H) a0) ((pr1 H) b)) =>
               precategory_fun_on_iso A C F a0 b
                 (iso_from_fully_faithful_reflection A B H Hff a0 b h) |}
        (pr1 (pr1 (lemma64_claim1 ((pr1 H) b))))
        (base_paths
           {|
           pr1 := {|
                  pr1 := (pr1 F) b;
                  pr2 := fun (a0 : A) (h : iso ((pr1 H) a0) ((pr1 H) b)) =>
                         precategory_fun_on_iso A C F a0 b
                           (iso_from_fully_faithful_reflection A B H Hff a0 b
                              h) |};
           pr2 := santas_little_helper b |}
           (pr1 (lemma64_claim1 ((pr1 H) b)))
           (pr2 (lemma64_claim1 ((pr1 H) b))
              {|
              pr1 := {|
                     pr1 := (pr1 F) b;
                     pr2 := fun (a0 : A) (h : iso ((pr1 H) a0) ((pr1 H) b)) =>
                            precategory_fun_on_iso A C F a0 b
                              (iso_from_fully_faithful_reflection A B H Hff
                                 a0 b h) |};
              pr2 := santas_little_helper b |}))))).
  
  Print identity_rect.
  simpl.
  
  rewrite toforallpaths_funextsec.
  generalize ((toforallpaths (fun _ : ob A => ob C) (pr1 (pr1 (GG O H))) (pr1 (pr1 F))
        pr1pr1functor a)).
  generalize (toforallpaths (fun _ : ob A => ob C) (pr1 (pr1 (GG O H))) (pr1 (pr1 F))
     pr1pr1functor b).
        intros i i0.
        elim i.
        elim i0.
  simpl
  unfold pr1pr1functor.
  simpl.
  generalize (pr1pr1functor).
  simpl.
  intro i.
  
  simpl.
  assert (HH : pr1 (pr1 (GG O H)) == pr1 (pr1 F)).
  simpl.
  apply funextsec; intro a0.
  set (kFa := fun (a : ob A) (h : iso (pr1 H a) (pr1 H a0)) =>
                precategory_fun_on_iso A C F _ _ 
                  (iso_from_fully_faithful_reflection _ _ H Hff _ _ h)).

  assert (HYpr2 : forall (t t' : total2 (fun a : ob A => iso ((pr1 H) a) ((pr1 H) a0)))
         (f : pr1 t --> pr1 t'),
              #(pr1 H) f;; pr2 t' == pr2 t ->
     #(pr1 F) f;; #(pr1 F) (fully_faithful_inv_hom A B H Hff (pr1 t') a0 (pr2 t')) ==
         #(pr1 F) (fully_faithful_inv_hom A B H Hff (pr1 t) a0 (pr2 t))).

(*  
*)
  simpl.
  intros [a h] [a' h'] f L.
  simpl in L; simpl.
  rewrite <- (precategory_fun_comp A C F).
  apply maponpaths.
  set (hhh':=equal_transport_along_weq _ _ (weq_from_fully_faithful A B H Hff a a0)
                 (f;; fully_faithful_inv_hom A B H Hff a' a0 h')                      
                 (fully_faithful_inv_hom A B H Hff a a0 h)  ).
  simpl in *.
  apply hhh'. clear hhh'.
  set (HFFaa := homotweqinvweq (weq_from_fully_faithful _ _ H Hff a a0)).
  unfold fully_faithful_inv_hom.
  simpl in *.
  rewrite HFFaa. clear HFFaa.
  rewrite precategory_fun_comp.
  set (HFFaa := homotweqinvweq (weq_from_fully_faithful _ _ H Hff a' a0)).
  unfold fully_faithful_inv_hom.
  simpl in *.
  rewrite HFFaa. clear HFFaa.
  apply L.
  
  set (HY := tpair _ (tpair _ (pr1 F a0) kFa) HYpr2 : X (pr1 H a0)).
  
  set (hula := pr2 (lemma64_claim1 (pr1 H a0)) HY ).
  set (hulapr2 := base_paths _ _ (base_paths _ _ hula)).
  simpl in hulapr2.
  apply pathsinv0.
  apply hulapr2.
  
  apply (total2_paths HH).
  induction HH.
  
  
  
  rewrite precategory_fun_id; apply idpath.
  
  

  
End preimage.

End essentially_surjective.

End lemma64.





