(************************************************************

Benedikt Ahrens and Chris Kapulkin
january 2013


************************************************************)


(************************************************************

Contents :  Definition of adjunction
	
	    Definition of equivalence of precategories
	
	    Equivalence of categories yields weak equivalence
            of object types
            
            A fully faithful and ess. surjective functor induces
            equivalence of precategories, if the source category 
            is saturated. 
           
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

(** * Adjunction *)


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

(** * Equivalence of (pre)categories *)

Definition equivalence_of_precats (A B : precategory)(F : precategory_objects [A, B]) : UU :=
   total2 (fun H : is_left_adjoint _ _ F =>
     dirprod (forall a, is_precat_isomorphism 
                    (eta_from_left_adjoint A B F H a))
             (forall b, is_precat_isomorphism
                    (eps_from_left_adjoint A B F H b))
             ).


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


(** * Equivalence of categories yields equivalence of object types *)
(**  Fundamentally needed that both source and target are saturated *)

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

   
(** If [F] is fully faithful, then being essentially surjective 
     is a proposition *)


Lemma isaprop_sigma_iso (A B : precategory) (HA : is_saturated A)
     (F : precategory_objects [A, B]) (HF : fully_faithful F) :
      forall b : precategory_objects B,
  isaprop (total2 (fun a : precategory_objects A => iso_precat (pr1 F a) b)).
Proof.
  intro b.
  apply invproofirrelevance.
  intros x x'.
  destruct x as [a f].
  destruct x' as [a' f'].
  set (fminusf := iso_comp f (iso_inv_from_iso f')).
  set (g := iso_from_fully_faithful_reflection _ _ _ HF _ _ fminusf).
  set (p := isotoid _ HA g).

  apply (total2_paths2 (B:=fun a' => iso_precat ((pr1 F) a') b) (isotoid _ HA g)).
  pathvia (iso_comp (iso_inv_from_iso 
    (precategory_fun_on_iso _ _ F _ _ (idtoiso (isotoid _ HA g)))) f).
  generalize (isotoid _ HA g).
  intro p0.
  induction p0.
  simpl.
  
  rewrite <- precategory_fun_on_iso_inv.
  rewrite iso_inv_of_iso_id.
  apply eq_iso_precat.
  simpl. 
  rewrite transportf_idpath.
  rewrite precategory_fun_id.
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


Lemma isaprop_pi_sigma_iso (A B : precategory) (HA : is_saturated A)
     (F : precategory_objects [A, B]) (HF : fully_faithful F) :
  isaprop (forall b : precategory_objects B, 
             total2 (fun a : precategory_objects A => iso_precat (pr1 F a) b)).
Proof.
  apply impred.
  intro b.
  apply isaprop_sigma_iso; assumption.
Qed.
   

(** * From full faithfullness and ess surj to equivalence *)

(** A fully faithful and ess. surjective functor induces an 
   equivalence of precategories, if the source category is 
    saturated. 
*)

Section from_fully_faithful_and_ess_surj_to_equivalence.

Variables A B : precategory.
Hypothesis HA : is_saturated A.
Variable F : precategory_objects [A, B].
Hypothesis HF : fully_faithful F.
Hypothesis HS : essentially_surjective F.

(** Definition of a functor which will later be the right adjoint. *)

Definition rad_ob : precategory_objects B -> precategory_objects A.
Proof.
  intro b.
  apply (pr1 (HS b (tpair (fun x => isaprop x) _ 
               (isaprop_sigma_iso A B HA F HF b)) (fun x => x))).
Defined.

(** Definition of the epsilon transformation *)

Definition rad_eps (b : precategory_objects B) : iso_precat (pr1 F (rad_ob b)) b.
Proof.
  apply (pr2 (HS b (tpair (fun x => isaprop x) _ 
               (isaprop_sigma_iso A B HA F HF b)) (fun x => x))).
Defined.

(** The right adjoint on morphisms *)

Definition rad_mor (b b' : precategory_objects B) (g : b --> b') : rad_ob b --> rad_ob b'.
Proof.
  
  set (epsgebs' := rad_eps b ;; g ;; iso_inv_from_iso (rad_eps b')).
  set (Gg := fully_faithful_inv_hom _ _ _ HF (rad_ob b) _ epsgebs').
  exact Gg.
Defined.

(** Definition of the eta transformation *)

Definition rad_eta (a : precategory_objects A) : a --> rad_ob (pr1 F a).
Proof.
  set (epsFa := inv_from_iso (rad_eps (pr1 F a))).
  exact (fully_faithful_inv_hom  _ _ _ HF _ _ epsFa).
Defined.

(** Above data specifies a functor *)

Definition rad_precategory_ob_mor_fun : precategory_ob_mor_fun B A.
Proof.
  exists rad_ob.
  exact rad_mor.
Defined.
  
Lemma rad_is_precategory_fun : is_precategory_fun rad_precategory_ob_mor_fun.
Proof.
  split; simpl.
  intro b.
  unfold rad_mor. simpl.
  rewrite precategory_id_right.
  rewrite iso_inv_after_iso.
  rewrite fully_faithful_inv_identity.
  apply idpath.
  
  intros a b c f g.
  unfold rad_mor; simpl.
  rewrite <- fully_faithful_inv_comp.
  apply maponpaths.
  repeat rewrite <- precategory_assoc.
  apply maponpaths.
  apply maponpaths.
  rewrite precategory_assoc.
  rewrite iso_after_iso_inv.
  rewrite precategory_id_left.
  apply idpath.
Qed.

Definition rad : precategory_objects [B, A].
Proof.
  exists rad_precategory_ob_mor_fun.
  apply rad_is_precategory_fun.
Defined.


(** Epsilon is natural *)

Lemma rad_eps_is_precategory_fun_fun : is_precategory_fun_fun 
    (pr1 (F O rad)) (precategory_fun_identity B)
       (fun b => rad_eps b).
Proof.
  unfold is_precategory_fun_fun.
  simpl.
  intros b b' g.
  unfold rad_mor.
  set (H3 := homotweqinvweq (weq_from_fully_faithful _ _ _ HF (pr1 rad b) (pr1 rad b'))).
  simpl in H3.
  unfold fully_faithful_inv_hom.
  simpl.
  rewrite H3.
  repeat rewrite <- precategory_assoc.
  rewrite iso_after_iso_inv.
  rewrite precategory_id_right.
  apply idpath.
Qed.

Definition rad_eps_trans : precategory_fun_fun _ _ :=
   tpair _ _ rad_eps_is_precategory_fun_fun.

(** Eta is natural *)

Lemma rad_eta_is_precategory_fun_fun : is_precategory_fun_fun 
         (precategory_fun_identity A) (pr1 (rad O F)) 
       (fun a => rad_eta a).
Proof.
  unfold is_precategory_fun_fun.
  simpl.
  intros a a' f.
  unfold rad_mor. simpl.
  set (h' := equal_transport_along_weq _ _ 
          (weq_from_fully_faithful _ _ _ HF a (rad_ob ((pr1 F) a')))).
  apply h'.
  simpl.
  rewrite precategory_fun_comp.
  rewrite precategory_fun_comp.
  unfold rad_eta.
  set (HHH := rad_eps_is_precategory_fun_fun (pr1 F a) (pr1 F a')).
  simpl in HHH.
  rewrite <- HHH.
  clear h'.
  clear HHH.


  set (H3 := homotweqinvweq (weq_from_fully_faithful _ _ _ HF a' (rad_ob ((pr1 F) a')))).
  simpl in H3.
  unfold fully_faithful_inv_hom. simpl.
  rewrite H3. clear H3.
  set (H3 := homotweqinvweq (weq_from_fully_faithful _ _ _ HF a (rad_ob ((pr1 F) a)))).
  simpl in H3.
  unfold fully_faithful_inv_hom. simpl.
  rewrite H3. clear H3.
  set (H3 := homotweqinvweq 
      (weq_from_fully_faithful _ _ _ HF (rad_ob (pr1 F a)) (rad_ob ((pr1 F) a')))).
  simpl in H3.
  unfold fully_faithful_inv_hom. simpl.
  rewrite H3.
  unfold rad_mor. simpl.
  repeat rewrite <- precategory_assoc.
  rewrite iso_inv_after_iso.
  rewrite precategory_id_right.
  unfold fully_faithful_inv_hom; simpl.
  rewrite H3.
  repeat rewrite precategory_assoc.
  rewrite iso_after_iso_inv. 
  rewrite precategory_id_left.
  apply idpath.
Qed.

Definition rad_eta_trans : precategory_fun_fun _ _ :=
   tpair _ _ rad_eta_is_precategory_fun_fun.


(** The data [rad], [eta], [eps] forms an adjunction *)

Lemma rad_form_adjunction : form_adjunction A B F rad rad_eta_trans rad_eps_trans.
Proof.
  split; simpl.
  intro a.
  unfold rad_eta. 
  set (H3 := homotweqinvweq 
      (weq_from_fully_faithful _ _ _ HF a (rad_ob (pr1 F a)) )).
  simpl in H3.
  unfold fully_faithful_inv_hom. simpl.
  rewrite H3.
  rewrite iso_after_iso_inv.
  apply idpath.
  
  intro b.
  
  set (h' := equal_transport_along_weq _ _ 
          (weq_from_fully_faithful _ _ _ HF (rad_ob b) (rad_ob b))).
       apply h'.
  simpl.
  rewrite precategory_fun_comp.
  set (Heta := precategory_fun_fun_ax _ _ rad_eta_trans).
  simpl in Heta.
  unfold rad_eta.
  unfold fully_faithful_inv_hom.
  simpl.
  set (H3 := homotweqinvweq 
      (weq_from_fully_faithful _ _ _ HF (rad_ob b) (rad_ob (pr1 F (rad_ob b))) )).
  simpl in H3.
  rewrite H3. clear H3.
  unfold rad_mor. unfold fully_faithful_inv_hom.
  simpl.
  set (H3 := homotweqinvweq 
      (weq_from_fully_faithful _ _ _ HF (rad_ob (pr1 F (rad_ob b))) 
                                        (rad_ob b))).
  simpl in H3.
  rewrite H3. clear H3.
  repeat rewrite precategory_assoc.
  rewrite iso_after_iso_inv.
  rewrite <- precategory_assoc.
  rewrite iso_inv_after_iso.
  rewrite precategory_id_left.
  rewrite precategory_fun_id.
  apply idpath.
Qed.
  
Definition rad_are_adjoints : are_adjoints _ _ F rad.
Proof.
  exists (dirprodpair rad_eta_trans rad_eps_trans).
  apply rad_form_adjunction.
Defined.

Definition rad_is_left_adjoint : is_left_adjoint _ _ F.
Proof.
  exists rad.
  apply rad_are_adjoints.
Defined.

(** Get an equivalence of precategories:

    remains to show that [eta], [eps] are isos
*)

Lemma rad_equivalence_of_precats : equivalence_of_precats _ _ F.
Proof.
  exists rad_is_left_adjoint.
  split; simpl.
  intro a.
  unfold rad_eta.
  set (H := fully_faithful_reflects_iso_proof _ _ _ HF
       a (rad_ob ((pr1 F) a))).
  simpl in *.
  set (H' := H (iso_inv_from_iso (rad_eps ((pr1 F) a)))).
  change ((fully_faithful_inv_hom A B F HF a (rad_ob ((pr1 F) a))
     (inv_from_iso (rad_eps ((pr1 F) a))))) with
      (fully_faithful_inv_hom A B F HF a (rad_ob ((pr1 F) a))
     (iso_inv_from_iso (rad_eps ((pr1 F) a)))).
  apply H'.
  
  intro b. apply (pr2 (rad_eps b)).
Defined.

End from_fully_faithful_and_ess_surj_to_equivalence.

 