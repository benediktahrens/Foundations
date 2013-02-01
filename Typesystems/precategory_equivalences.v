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

Notation "a == b" := (paths a b) (at level 70, no associativity).
Notation "! p " := (pathsinv0 p) (at level 50).
Notation "p @ q" := (pathscomp0 p q) (at level 60, right associativity).

Ltac pathvia b := (apply (@pathscomp0 _ _ b _ )).

Local Notation "a --> b" := (precategory_morphisms a b)(at level 50).
(*Local Notation "'hom' C" := (precategory_morphisms (C := C)) (at level 2).*)
Local Notation "f ;; g" := (precategory_compose f g)(at level 50).
Notation "[ C , D ]" := (precategory_fun_precategory C D).
Local Notation "# F" := (precategory_ob_mor_fun_morphisms F)(at level 3).

Definition functor_composite (A B C : precategory) (F : precategory_objects [A, B])
      (G : precategory_objects [B , C]) : precategory_objects [A , C] := 
   precategory_fun_composite _ _ _ F G.

Notation "G 'O' F" := (functor_composite _ _ _ F G) (at level 25).

(** * Whiskering: Composition of a natural transformation with a functor *)

Lemma is_precat_fun_fun_pre_whisker (A B C : precategory) (F : precategory_objects [A, B])
   (G H : precategory_objects [B, C]) (gamma : G --> H) : 
  is_precategory_fun_fun (precategory_fun_composite _ _ _ F G ) 
                         (precategory_fun_composite _ _ _ F H) 
     (fun a : precategory_objects A => pr1 gamma ((pr1 F) a)).
Proof.
  unfold is_precategory_fun_fun.
  simpl.
  intros x x' f.
  rewrite  (precategory_fun_fun_ax _ _ gamma).
  apply idpath.
Qed.

Definition pre_whisker (A B C : precategory) (F : precategory_objects [A, B])
   (G H : precategory_objects [B, C]) (gamma : G --> H) : 
       G O F --> H O F.
Proof.
  exists (fun a => pr1 gamma (pr1 F a)).
  apply is_precat_fun_fun_pre_whisker.
Defined.




Lemma is_precat_fun_fun_post_whisker (B C D : precategory) 
   (G H : precategory_objects [B, C]) (gamma : G --> H) 
        (K : precategory_objects [C, D]): 
  is_precategory_fun_fun (precategory_fun_composite _ _ _ G K) 
                         (precategory_fun_composite _ _ _ H K) 
     (fun a : precategory_objects B => # (pr1 K) (pr1 gamma  a)).
Proof.
  unfold is_precategory_fun_fun.
  simpl in *.
  intros x x' f.
  repeat rewrite <- precategory_fun_comp.
  rewrite  (precategory_fun_fun_ax _ _ gamma).
  apply idpath.
Qed.

Definition post_whisker (B C D : precategory) 
   (G H : precategory_objects [B, C]) (gamma : G --> H) 
        (K : precategory_objects [C, D]) : K O G --> K O H.
Proof.
  exists (fun a : precategory_objects B => # (pr1 K) (pr1 gamma  a)).
  apply is_precat_fun_fun_post_whisker.
Defined.


Definition form_adjunction (A B : precategory) (F : precategory_objects [A, B])
       (G : precategory_objects [B, A]) 
       (eta : precategory_fun_fun (precategory_fun_identity A) (pr1 (G O F)))  
       (eps : precategory_fun_fun (pr1 (F O G)) (precategory_fun_identity B)) : UU :=
dirprod 
  (forall a : precategory_objects A,
       # (pr1 F) (pr1 eta a) ;;   pr1 eps (pr1 F a) == precategory_identity (pr1 F a))
  (forall b : precategory_objects B,
       pr1 eta (pr1 G b) ;; # (pr1 G) (pr1 eps b) == precategory_identity (pr1 G b)).

Definition are_adjoints (A B : precategory) (F : precategory_objects [A, B])
    (G : precategory_objects [B, A]) : UU :=
  total2 (fun etaeps : dirprod 
            (precategory_fun_fun (precategory_fun_identity A) (pr1 (G O F)))
            (precategory_fun_fun (pr1 (F O G)) (precategory_fun_identity B)) =>
      form_adjunction A B F G (pr1 etaeps) (pr2 etaeps)).

Definition is_left_adjoint (A B : precategory) (F : precategory_objects [A, B]) : UU :=
   total2 (fun G : precategory_objects [B, A] => are_adjoints A B F G).

Definition right_adjoint (A B : precategory) (F : precategory_objects [A, B]) 
      (H : is_left_adjoint _ _ F) : precategory_objects [B, A] := pr1 H.

Definition eta_from_left_adjoint (A B : precategory) (F : precategory_objects [A, B]) 
      (H : is_left_adjoint _ _ F) : 
  precategory_fun_fun (precategory_fun_identity A) (pr1 (pr1 H O F)) := pr1 (pr1 (pr2 H)).


Definition eps_from_left_adjoint (A B : precategory) (F : precategory_objects [A, B]) 
      (H : is_left_adjoint _ _ F)  : 
 precategory_fun_fun (pr1 (F O pr1 H)) (precategory_fun_identity B)
   := pr2 (pr1 (pr2 H)).


Definition triangle_id_left_ad (A B : precategory) (F : precategory_objects [A, B]) 
      (H : is_left_adjoint _ _ F) :
  forall (a : precategory_objects A),
       #(pr1 F) (pr1 (pr1 (pr1 (pr2 H))) a);;
       pr1 (pr2 (pr1 (pr2 H))) ((pr1 F) a) ==
       precategory_identity ((pr1 F) a) := pr1 (pr2 (pr2 H)).

Definition triangle_id_right_ad (A B : precategory) (F : precategory_objects [A, B]) 
      (H : is_left_adjoint _ _ F) :
  forall b : precategory_objects B,
        pr1 (pr1 (pr1 (pr2 H))) ((pr1 (pr1 H)) b);;
        #(pr1 (pr1 H)) (pr1 (pr2 (pr1 (pr2 H))) b) ==
        precategory_identity ((pr1 (pr1 H)) b)
   := pr2 (pr2 (pr2 H)).


Definition equivalence_of_precats (A B : precategory)(F : precategory_objects [A, B]) : UU :=
   total2 (fun H : is_left_adjoint _ _ F =>
     dirprod (forall a, is_precat_isomorphism 
                    (eta_from_left_adjoint A B F H a))
             (forall b, is_precat_isomorphism
                    (eps_from_left_adjoint A B F H b))
             ).

Print iso_precat.
Definition eta_iso_from_equivalence_of_precats (A B : precategory)
  (F : precategory_objects [A, B]) (HF : equivalence_of_precats _ _ F) : 
       iso_precat (C:=[A, A]) (precategory_fun_identity A) 
                              (right_adjoint _ _ _ (pr1 HF) O F).
Proof.
  exists (eta_from_left_adjoint _ _ _ (pr1 HF)).
  apply precategory_fun_iso_if_pointwise_iso.
  apply (pr1 (pr2 HF)).
Defined.

Definition eps_iso_from_equivalence_of_precats (A B : precategory)
  (F : precategory_objects [A, B]) (HF : equivalence_of_precats _ _ F) : 
       iso_precat (C:=[B, B]) (F O right_adjoint _ _ _ (pr1 HF))
                (precategory_fun_identity B).
Proof.
  exists (eps_from_left_adjoint _ _ _ (pr1 HF)).
  apply precategory_fun_iso_if_pointwise_iso.
  apply (pr2 (pr2 HF)).
Defined.

Lemma equiv_of_cats_is_weq_of_objects (A B : precategory)
   (HA : is_saturated A) (HB : is_saturated B) (F : precategory_objects [A, B])
   (HF : equivalence_of_precats A B F) : 
     isweq (pr1 (pr1 F)).
Proof.
  set (G := right_adjoint _ _ _ (pr1 HF)).
  set (et := eta_iso_from_equivalence_of_precats _ _ _ HF).
  set (ep := eps_iso_from_equivalence_of_precats _ _ _ HF).
  set (AAsat := is_saturated_functor_category A _ HA).
  set (BBsat := is_saturated_functor_category B _ HB).
  set (Et := isotoid _ AAsat et).
  set (Ep := isotoid _ BBsat ep).
  apply (gradth _ (fun b => pr1 (right_adjoint A B F (pr1 HF)) b)).
  intro a.
  set (ou := toforallpaths _ _ _ (base_paths _ _ (base_paths _ _ Et)) a).
  simpl in ou.
  apply (! ou).
  intro y.
  set (ou := toforallpaths _ _ _ (base_paths _ _ (base_paths _ _ Ep)) y).
  apply ou.
Qed.

Definition weq_on_objects_from_equiv_of_cats (A B : precategory)
   (HA : is_saturated A) (HB : is_saturated B) (F : precategory_objects [A, B])
   (HF : equivalence_of_precats A B F) : weq 
          (precategory_objects A) (precategory_objects B).
Proof.
  exists (pr1 (pr1 F)).
  apply equiv_of_cats_is_weq_of_objects; assumption.
Defined.



Lemma bla  (A B : precategory) (F : precategory_objects [A, B]) 
          (a : precategory_objects A) :
inv_from_iso (precategory_fun_on_iso A B F a a (identity_iso_precat a))
  == precategory_identity _ .
Proof.
  assert (H' : precategory_fun_on_iso A B F a a (identity_iso_precat a) == 
           identity_iso_precat _ ).
  apply eq_iso_precat.
  simpl.
  apply precategory_fun_id.
  rewrite H'.
  apply idpath.
Qed.

  
    


Lemma isaprop_pi_sigma_iso (A B : precategory) (HA : is_saturated A)
     (F : precategory_objects [A, B]) (HF : fully_faithful F) :
  isaprop (forall b : precategory_objects B, 
             total2 (fun a : precategory_objects A => iso_precat (pr1 F a) b)).
Proof.
  apply impred.
  intro b.
  apply invproofirrelevance.
  intros x x'.
  destruct x as [a f].
  destruct x' as [a' f'].
  set (fminusf := iso_comp f (iso_inv_from_iso f')).
  set (g := iso_from_fully_faithful_reflection _ _ _ HF _ _ fminusf).
  set (p := isotoid _ HA g).
  Print total2_paths2.
  apply (total2_paths2 (B:=fun a' => iso_precat ((pr1 F) a') b) (isotoid _ HA g)).
  pathvia (iso_comp (iso_inv_from_iso 
    (precategory_fun_on_iso _ _ F _ _ (idtoiso (isotoid _ HA g)))) f).
  generalize (isotoid _ HA g).
  intro p0.
  induction p0.
  simpl.
  
  apply eq_iso_precat.
  simpl. 
  rewrite transportf_idpath.
  rewrite bla.
  rewrite precategory_id_left.
  apply idpath.
  
  rewrite idtoiso_isotoid.
  unfold g.
  unfold fminusf.
  simpl.
  clear p.
  clear g.
  clear fminusf.
  assert (HFg : precategory_fun_on_iso A B F a a'
        (iso_from_fully_faithful_reflection A B F HF a a'
           (iso_comp f (iso_inv_from_iso f'))) == 
           iso_comp f (iso_inv_from_iso f')).
  generalize (iso_comp f (iso_inv_from_iso f')).
  intro h.
  set (HH := weq_from_fully_faithful _ _ _ HF a a').
  apply eq_iso_precat.
  simpl.
  set (H3 := homotweqinvweq (weq_from_fully_faithful _ _ _ HF a a')).
  simpl in H3.
  set (H' := HF a a').
  unfold fully_faithful_inv_hom.
  unfold invweq.
  simpl.
  rewrite H3.
  apply idpath.
  
  rewrite HFg.
  rewrite iso_inv_of_iso_comp.
  apply eq_iso_precat.
  simpl.
  repeat rewrite <- precategory_assoc.
  rewrite iso_after_iso_inv.
  rewrite precategory_id_right.
  set (H := iso_inv_iso_inv _ _ _ f').
  set (h':= base_paths _ _ H).
  assumption.
Qed.
  
  

  simpl.
  unfold HH .
  destruct H' a.
  
  apply eq_iso_precat.
  simpl.
  
  apply eq_iso_precat.
  
  clear p.
  clear g.
  clear fminusf.
  clear f'.
  
  apply idpath.
  Print identity_iso_precat.
(*  unfold inv_from_iso. simpl.*)
  unfold precategory_fun_on_iso.
 Print identity_iso_precat.
  unfold identity_iso_precat.
  simpl.
  rewrite precategory_fun_id.
  unfold identity_iso_precat.
  unfold inv_from_iso.
  simpl.
  
  simpl.
  clear g.
  induction p.
  simpl.
  pathvia h.
  
  
  
  
  assert (H' : pr1 x == pr1 x').
    
  apply (total2_paths




(*
Definition left_adjoint (C D : precategory) (F : precategory_object [C,D]) :=
   total2
*)