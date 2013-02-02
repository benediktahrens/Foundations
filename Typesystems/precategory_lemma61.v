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


Section lemma61.

Variables A B C : precategory.
Variable H : precategory_objects [A, B].
Hypothesis p : essentially_surjective H.
Hypothesis Hff : fully_faithful H.

Lemma claim1 (F G : precategory_objects [B, C]) (gamma : F O H --> G O H) 
        (b : precategory_objects B) : 
   iscontr (total2 (fun g : pr1 F b --> pr1 G b => 
      forall a : precategory_objects A, forall f : iso_precat (pr1 H a) b,
           pr1 gamma a == #(pr1 F) f ;; g ;; #(pr1 G) (inv_from_iso f)  )).
Proof.
  Check isapropiscontr.
  set (X := isapropiscontr (total2
     (fun g : (pr1 F) b --> (pr1 G) b =>
      forall (a : precategory_objects A) (f : iso_precat ((pr1 H) a) b),
      pr1 gamma a == (#(pr1 F) f;; g);; #(pr1 G) (inv_from_iso f)))).
  set (pbX := p b (tpair (fun x => isaprop x) _ X)).
  simpl.
  apply pbX. clear pbX. simpl. clear X.
  intro anoth.
  destruct anoth as [anot h].
  simpl in *.
  set (g := #F (inv_from_iso h) ;; gamma anot ;; #G h).

  assert (gp : forall (a : precategory_objects A) 
                     (f : iso_precat (H a) b),
                 gamma a == #F f ;; g ;; #G (inv_from_iso f)).
  intros a f.
  set (k := iso_from_fully_faithful_reflection _ _ _ Hff _ _ 
             (iso_comp f (iso_inv_from_iso h))).
  set (GHk := precategory_fun_on_iso _ _ G _ _ 
                (precategory_fun_on_iso _ _ H _ _ k)).
  pathvia (#F (#H k) ;; gamma anot ;; iso_inv_from_iso GHk).
  
  set (P := post_comp_with_iso_is_inj _ _ _ GHk (pr2 GHk)).
  apply P.
  rewrite <- precategory_assoc.
  change (iso_inv_from_iso GHk ;; GHk) with (inv_from_iso GHk ;; GHk).
  rewrite iso_after_iso_inv. rewrite precategory_id_right.
  set (Hgamma := precategory_fun_fun_ax _ _ gamma).
  simpl in Hgamma.
  rewrite Hgamma. apply idpath.
  unfold GHk.
  rewrite <- precategory_fun_on_iso_inv.
  unfold k. simpl.
  rewrite precategory_fun_on_iso_iso_from_fully_faithful_reflection.
  set (Hr := iso_inv_of_iso_comp _ _ _ _ f (iso_inv_from_iso h)).
  simpl in Hr. 
  set (Hrp := base_paths _ _ Hr). simpl in Hrp.
  rewrite Hrp.
  rewrite precategory_fun_comp.
  set (H3 := homotweqinvweq (weq_from_fully_faithful _ _ _ Hff a anot)).
  simpl in H3. unfold fully_faithful_inv_hom.
  simpl. rewrite H3. clear H3.
  set (H4 := base_paths _ _ (iso_inv_iso_inv _ _ _ h)).
  simpl in H4. rewrite H4.
  rewrite precategory_fun_comp.
  unfold g.
  repeat rewrite precategory_assoc.
  apply idpath.
  
  exists bla.



Lemma claim1 (F G : precategory_objects [B, C]) (gamma : F O H --> G O H) 
        (b : precategory_objects B) : 
   iscontr (total2 (fun g : pr1 F b --> pr1 G b => 
      forall a : precategory_objects A, forall f : iso_precat (pr1 H a) b,
           pr1 gamma a == #(pr1 F) f ;; g ;; #(pr1 G) (inv_from_iso f)  )).
Proof.
  Check isapropiscontr.
  set (X := isapropiscontr (total2
     (fun g : (pr1 F) b --> (pr1 G) b =>
      forall (a : precategory_objects A) (f : iso_precat ((pr1 H) a) b),
      pr1 gamma a == (#(pr1 F) f;; g);; #(pr1 G) (inv_from_iso f)))).
  set (pbX := p b (tpair (fun x => isaprop x) _ X)).
  simpl.
  apply pbX. clear pbX. simpl. clear X.
  intro anoth.
  destruct anoth as [anot h].
  simpl in *.
  set (g := #F (inv_from_iso h) ;; gamma anot ;; #G h).

  assert (gp : forall (a : precategory_objects A) 
                     (f : iso_precat (H a) b),
                 gamma a == #F f ;; g ;; #G (inv_from_iso f)).
  intros a f.
  set (k := iso_from_fully_faithful_reflection _ _ _ Hff _ _ 
             (iso_comp f (iso_inv_from_iso h))).
  set (GHk := precategory_fun_on_iso _ _ G _ _ 
                (precategory_fun_on_iso _ _ H _ _ k)).
  pathvia (#F (#H k) ;; gamma anot ;; iso_inv_from_iso GHk).
  
  set (P := post_comp_with_iso_is_inj _ _ _ GHk (pr2 GHk)).
  apply P.
  rewrite <- precategory_assoc.
  change (iso_inv_from_iso GHk ;; GHk) with (inv_from_iso GHk ;; GHk).
  rewrite iso_after_iso_inv. rewrite precategory_id_right.
  set (Hgamma := precategory_fun_fun_ax _ _ gamma).
  simpl in Hgamma.
  rewrite Hgamma. apply idpath.
  unfold GHk.
  rewrite <- precategory_fun_on_iso_inv.
  unfold k. simpl.
  rewrite precategory_fun_on_iso_iso_from_fully_faithful_reflection.
  set (Hr := iso_inv_of_iso_comp _ _ _ _ f (iso_inv_from_iso h)).
  simpl in Hr. 
  set (Hrp := base_paths _ _ Hr). simpl in Hrp.
  rewrite Hrp.
  rewrite precategory_fun_comp.
  set (H3 := homotweqinvweq (weq_from_fully_faithful _ _ _ Hff a anot)).
  simpl in H3. unfold fully_faithful_inv_hom.
  simpl. rewrite H3. clear H3.
  set (H4 := base_paths _ _ (iso_inv_iso_inv _ _ _ h)).
  simpl in H4. rewrite H4.
  rewrite precategory_fun_comp.
  unfold g.
  repeat rewrite precategory_assoc.
  apply idpath.
  
  exists bla.
  
  rewrite iso_inv_iso_inv.
  rewrite precategory_fun_on_iso_comp.
  rewrite <- precategory_fun_fun_ax.
set (HHH := iso_after_iso_inv _ _ _ GHk).
  unfold inv_from_iso in HHH. 
  unfold iso_inv_from_iso. simpl. rewrite HHH.
  simpl.

  simpl.
  
                
  set (fff := #F (#H k) ;; gamma anot ). simpl in *. 
  set (fffGhK := fff ;; iso_inv_from_iso GHk) . simpl in fff.   
  pathvia (#F (#H k) ;; gamma anot ;; pr1 GHk).
  
  


















