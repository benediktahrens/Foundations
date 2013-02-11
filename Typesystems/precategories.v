(************************************************************

Benedikt Ahrens and Chris Kapulkin
january 2013


************************************************************)


(************************************************************

Contents :  Definition of 
		Precategories, 
	        Categories (saturated precategories)         	
                Setcategories
                
                Isomorphisms
                  various lemmas:
                    uniqueness of inverse, composition etc.
                    stability under composition
                
                Categories have groupoid as objects
                
                Subcategories, Full subcats
                

		Functors
                  preserve isos, inverses
                                    
                  fully faithful functors
                    preserve isos, inverses, composition 
                            backwards
                    
                  essentially surjective
                  faithful
                  full
                  fully faithful == full and faithful
                  
                  Image of a functor, full subcat specified
                                       by a functor
                  
                  Subcategories, back to
                    Inclusion functor
                    Full image of a functor
                    Factorization of a functor via its
                       full image
                    This factorization is fully faithful
                       if the functor is
                       [precategory_fun_full_img_fully_faithful_if_fun_is]
                                           
                    Isos in full subcategory are equiv
                      to isos in the precategory

                    Full subcategory of a category is 
                      a category
                      [is_saturated_full_subcat]
                      
                      
		Natural transformations
                  Equality is pointwise equality.
                  
                  
		Functor (pre)category			
                  Isomorphisms in functor category are pointwise
                         isomorphisms
                         
                Isomorphic Functors are equal
                   if target precategory is saturated
                   [functor_eq_from_functor_iso]
                  
                Functor precategory is saturated if
                   target precategory is
                   [is_saturated_functor_category]
		
		
	
	   
           
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

Notation "a == b" := (paths a b) (at level 70, no associativity).
Notation "! p " := (pathsinv0 p) (at level 50).
Notation "p @ q" := (pathscomp0 p q) (at level 60, right associativity).

Ltac pathvia b := (apply (@pathscomp0 _ _ b _ )).

(** * Definition of a precategory *)
(** ** Space of types (objects) together with a fibration (morphisms) *)

Definition precategory_ob_mor := total2 (
  fun ob : UU => ob -> ob -> hSet).

Definition precategory_ob_mor_pair (ob : UU)(mor : ob -> ob -> hSet) :
    precategory_ob_mor := tpair _ ob mor.

Definition precategory_objects (C : precategory_ob_mor) : UU := @pr1 _ _ C.
Coercion precategory_objects : precategory_ob_mor >-> UU.

Definition precategory_morphisms { C : precategory_ob_mor } : 
      precategory_objects C -> precategory_objects C -> hSet :=
    pr2 C.

(** We introduce notation for morphisms *)
(** in order for this notation not to pollute subsequent files, 
    we define this notation locally *)

Local Notation "a --> b" := (precategory_morphisms a b)(at level 50).

(** ** [precategory_data] *)
(** data of a precategory : 
    - objects
    - morphisms
    - identity morphisms
    - composition
*)

Definition precategory_data := total2 (
   fun C : precategory_ob_mor =>
     dirprod (forall c : precategory_objects C, 
                precategory_morphisms c c) (* identities *) 
             (forall a b c : precategory_objects C,
                (*precategory_morphisms*) a --> b ->
                (*precategory_morphisms*) b --> c ->
                (*precategory_morphisms*) a --> c)).

Definition precategory_data_pair (C : precategory_ob_mor)
    (id : forall c : precategory_objects C, 
                precategory_morphisms c c)
    (comp: forall a b c : precategory_objects C,
         a --> b -> b --> c -> a --> c) : precategory_data :=
   tpair _ C (dirprodpair id comp).

Definition precategory_ob_mor_from_precategory_data (C : precategory_data) :
     precategory_ob_mor := pr1 C.
Coercion precategory_ob_mor_from_precategory_data : 
  precategory_data >-> precategory_ob_mor.

Definition precategory_identity { C : precategory_data } :
    forall c : precategory_objects C, c --> c := 
         pr1 (pr2 C).

Definition precategory_compose { C : precategory_data } 
  { a b c : precategory_objects C } : 
    a --> b -> b --> c -> a --> c := pr2 (pr2 C) a b c.

Local Notation "f ;; g" := (precategory_compose f g)(at level 50).


(** *** Axioms of a precategory *)
(** 
        - identity is left and right neutral for composition 
        - composition is associative
*)

Definition is_precategory (C : precategory_data) := 
   dirprod (dirprod (forall (a b : precategory_objects C) (f : a --> b),
                         precategory_identity a ;; f == f)
                     (forall (a b : precategory_objects C) (f : a --> b),
                         f ;; precategory_identity b == f))
            (forall (a b c d : precategory_objects C) 
                    (f : a --> b)(g : b --> c) (h : c --> d),
                     f ;; (g ;; h) == (f ;; g) ;; h).

Definition precategory := total2 is_precategory.

Definition precategory_data_from_precategory (C : precategory) : 
       precategory_data := pr1 C.
Coercion precategory_data_from_precategory : precategory >-> precategory_data.

Definition precategory_id_left (C : precategory) : 
   forall (a b : precategory_objects C) (f : a --> b),
           precategory_identity a ;; f == f := pr1 (pr1 (pr2 C)).

Definition precategory_id_right (C : precategory) :
   forall (a b : precategory_objects C) (f : a --> b),
           f ;; precategory_identity b == f := pr2 (pr1 (pr2 C)).

Definition precategory_assoc (C : precategory) : 
   forall (a b c d : precategory_objects C) 
          (f : a --> b)(g : b --> c) (h : c --> d),
                     f ;; (g ;; h) == (f ;; g) ;; h := pr2 (pr2 C).

(** Any equality on objects a and b induces a morphism from a to b *)

Definition precategory_eq_morphism (C : precategory_data)
 (a b : precategory_objects C) (H : a == b) : a --> b.
Proof.
  destruct H.
  exact (precategory_identity a).
Defined.

Definition precategory_eq_morphism_inv (C : precategory_data) 
    (a b : precategory_objects C) (H : a == b) : b --> a.
Proof.
  destruct H.
  exact (precategory_identity a).
Defined.



(** ** Setcategories: Precategories whose objects form a set *)

Definition setcategory := total2 (
   fun C : precategory => isaset (precategory_objects C)).

Definition precategory_from_setcategory (C : setcategory) : precategory := pr1 C.
Coercion precategory_from_setcategory : setcategory >-> precategory.

Definition setcategory_objects_set (C : setcategory) : hSet :=
    hSetpair (precategory_objects C) (pr2 C).

Lemma precategory_eq_morphism_pi (C : setcategory) (a b : precategory_objects C)
      (H H': a == b) : precategory_eq_morphism C a b H == 
                       precategory_eq_morphism C a b H'.
Proof.
  assert (h : H == H').
  apply uip. apply (pr2 C).
  apply (maponpaths (precategory_eq_morphism C a b) h).
Qed.

(** ** Isomorphisms in a precategory *)

Definition is_inverse_in_precat {C : precategory} {a b : precategory_objects C}
  (f : a --> b) (g : b --> a) := 
  dirprod (f ;; g == precategory_identity a)
          (g ;; f == precategory_identity b).

Lemma isaprop_is_inverse_in_precat (C : precategory) (a b : precategory_objects C)
   (f : a --> b) (g : b --> a) : isaprop (is_inverse_in_precat f g).
Proof.
  apply isapropdirprod.
  apply (pr2 (a --> a)).
  apply (pr2 (b --> b)).
Qed.

Lemma inverse_unique_precat (C : precategory) (a b : precategory_objects C)
   (f : a --> b) (g g': b --> a) (H : is_inverse_in_precat f g)
    (H' : is_inverse_in_precat f g') : g == g'.
Proof.
  destruct H as [eta eps].
  destruct H' as [eta' eps'].
  assert (H : g == precategory_identity b ;; g).
    rewrite precategory_id_left; apply idpath.
  apply (pathscomp0 H).
  rewrite <- eps'.
  rewrite <- precategory_assoc.
  rewrite eta.
  apply precategory_id_right.
Qed.

Definition is_inverse_in_precat_hProp {C : precategory} 
        {a b : precategory_objects C}
  (f : a --> b) (g : b --> a) : hProp := 
   hProppair _ (isaprop_is_inverse_in_precat C a b f g).

Definition is_precat_isomorphism {C : precategory} {a b : precategory_objects C}
  (f : a --> b) := total2 (fun g => is_inverse_in_precat_hProp f g).

Lemma isaprop_is_precat_isomorphism {C : precategory} {a b : precategory_objects C}
     (f : a --> b) : isaprop (is_precat_isomorphism f).
Proof.
  apply invproofirrelevance.
  intros g g'.
  set (Hpr1 := inverse_unique_precat _ _ _ _ _ _ (pr2 g) (pr2 g')).
  apply (total2_paths Hpr1).
  destruct g as [g [eta eps]].
  destruct g' as [g' [eta' eps']].
  simpl in *.
  apply pairofobuip.
Qed.


Definition iso_precat {C : precategory} (a b :precategory_objects C) := total2
    (fun f : a --> b => is_precat_isomorphism f).

Lemma eq_iso_precat (C : precategory)(a b : precategory_objects C)
   (f g : iso_precat a b) : pr1 f == pr1 g -> f == g.
Proof.
  intro H.
  apply (total2_paths H).
  apply proofirrelevance.
  apply isaprop_is_precat_isomorphism.
Qed.

Definition arrow_from_iso (C : precategory)(a b : precategory_objects C) 
   (f : iso_precat a b) : a --> b := pr1 f.
Coercion arrow_from_iso : iso_precat >-> pr1hSet.

Lemma isaset_iso_precat {C : precategory} (a b :precategory_objects C) :
  isaset (iso_precat a b).
Proof.
  change isaset with (isofhlevel 2).
  apply isofhleveltotal2.
  apply (pr2 (a --> b)).
  intro f.
  apply isasetaprop.
  apply isaprop_is_precat_isomorphism.
Qed.

Lemma identity_is_iso_precat (C : precategory) (a : precategory_objects C) :
    is_precat_isomorphism (precategory_identity a).
Proof.
  exists (precategory_identity a).
  simpl; split;
  apply precategory_id_left.
Defined.

Definition identity_iso_precat {C : precategory} (a : precategory_objects C) :
   iso_precat a a := tpair _ _ (identity_is_iso_precat C a).

Definition inv_from_iso {C : precategory} {a b : precategory_objects C}
  (f : iso_precat a b) : b --> a := pr1 (pr2 f).

Lemma is_iso_inv_from_iso {C : precategory} (a b : precategory_objects C)
  (f : iso_precat a b) : is_precat_isomorphism (inv_from_iso f).
Proof.
  exists (pr1 f).
  simpl; split; simpl.
  apply (pr2 (pr2 f)).
  apply (pr2 (pr2 f)).
Qed.

Definition iso_inv_from_iso {C : precategory} {a b : precategory_objects C}
  (f : iso_precat a b) : iso_precat b a.
Proof.
  exists (inv_from_iso f).
  apply is_iso_inv_from_iso.
Defined.


Definition iso_inv_after_iso (C : precategory) (a b : precategory_objects C)
   (f : iso_precat a b) : f;; inv_from_iso f == precategory_identity _ :=
      pr1 (pr2 (pr2 f)).

Definition iso_after_iso_inv (C : precategory) (a b : precategory_objects C)
   (f : iso_precat a b) : inv_from_iso f ;; f == precategory_identity _ :=
      pr2 (pr2 (pr2 f)).


Lemma iso_inv_on_right (C : precategory) (a b c: precategory_objects C)
  (f : iso_precat a  b) (g : b --> c) (h : a --> c) (H : h == f;;g) :
     inv_from_iso f ;; h == g.
Proof.
  assert (H2 : inv_from_iso f;; h == 
                  inv_from_iso f;; (f ;; g)).
  apply maponpaths; assumption.
  rewrite precategory_assoc in H2.
  rewrite H2.
  rewrite iso_after_iso_inv.
  apply precategory_id_left.
Qed.

Lemma iso_inv_on_left (C : precategory) (a b c: precategory_objects C)
  (f : a --> b) (g : iso_precat b c) (h : a --> c) (H : h == f;;g) :
     f == h ;; inv_from_iso g.
Proof.
  assert (H2 : h ;; inv_from_iso g == 
                         (f;; g) ;; inv_from_iso g).
    rewrite H. apply idpath.
  rewrite <- precategory_assoc in H2.
  rewrite iso_inv_after_iso in H2.
  rewrite precategory_id_right in H2.
  apply pathsinv0.
  assumption.
Qed.



Lemma is_iso_comp_of_isos {C : precategory} {a b c : precategory_objects C}
  (f : iso_precat a b) (g : iso_precat b c) : is_precat_isomorphism (f ;; g).
Proof.
  exists (inv_from_iso g ;; inv_from_iso f).
  simpl; split; simpl;
  unfold inv_from_iso; simpl.
  destruct f as [f [f' Hf]]. simpl in *.
  destruct g as [g [g' Hg]]; simpl in *.
  pathvia ((f ;; (g ;; g')) ;; f').
  repeat rewrite precategory_assoc; apply idpath.
  rewrite (pr1 Hg).
  rewrite precategory_id_right.
  rewrite (pr1 Hf).
  apply idpath.

  destruct f as [f [f' Hf]]. simpl in *.
  destruct g as [g [g' Hg]]; simpl in *.
  pathvia ((g' ;; (f' ;; f)) ;; g).
  repeat rewrite precategory_assoc; apply idpath.
  rewrite (pr2 Hf).
  rewrite precategory_id_right.
  rewrite (pr2 Hg).
  apply idpath.
Qed.


Definition iso_comp {C : precategory} {a b c : precategory_objects C}
  (f : iso_precat a b) (g : iso_precat b c) : iso_precat a c.
Proof.
  exists (f ;; g).
  apply is_iso_comp_of_isos.
Defined.

Lemma inv_iso_unique (C : precategory) (a b : precategory_objects C)
  (f : iso_precat a b) (g : iso_precat b a) :
  is_inverse_in_precat f g -> g == iso_inv_from_iso f.
Proof.
  intro H.
  apply eq_iso_precat.
  apply (inverse_unique_precat _ _ _ f).
  assumption.
  split.
  apply iso_inv_after_iso.
  set (h := iso_after_iso_inv _ _ _ f).
  unfold iso_inv_from_iso.
  simpl in *.
  apply h.
Qed.


Lemma iso_inv_of_iso_comp (C : precategory) (a b c : precategory_objects C)
   (f : iso_precat a b) (g : iso_precat b c) :
   iso_inv_from_iso (iso_comp f g) == iso_comp (iso_inv_from_iso g) (iso_inv_from_iso f).
Proof.
  apply pathsinv0.
  apply inv_iso_unique.
  split; simpl.
  pathvia (f ;; (g ;; inv_from_iso g) ;; inv_from_iso f).
  repeat rewrite precategory_assoc. apply idpath.
  rewrite iso_inv_after_iso.
  rewrite precategory_id_right.
  apply iso_inv_after_iso.
  
  pathvia ((inv_from_iso g;; (inv_from_iso f;; f);; g)).
  repeat rewrite precategory_assoc. apply idpath.
  rewrite iso_after_iso_inv.
  rewrite precategory_id_right.
  apply iso_after_iso_inv.
Qed.

Lemma iso_inv_of_iso_id (C : precategory) (a : precategory_objects C) :
   iso_inv_from_iso (identity_iso_precat a) == identity_iso_precat a.
Proof.
  apply pathsinv0.
  apply inv_iso_unique.
  split; simpl; rewrite precategory_id_left;
  apply idpath.
Qed.


Lemma iso_inv_iso_inv (C : precategory) (a b : precategory_objects C)
   (f : iso_precat a b) : 
     iso_inv_from_iso (iso_inv_from_iso f) == f.
Proof.
  apply pathsinv0.
  apply inv_iso_unique.
  split; simpl.
  apply iso_after_iso_inv.
  apply iso_inv_after_iso.
Qed.


Lemma pre_comp_with_iso_is_inj (C : precategory) (a b c : precategory_objects C)
    (f : a --> b) (H : is_precat_isomorphism f) (g h : b --> c) : f ;; g == f ;; h -> g == h.
Proof.
  intro HH.
  pathvia (pr1 H ;; f ;; g).
  rewrite (pr2 (pr2 H)).
  rewrite precategory_id_left.
  apply idpath.
  pathvia ((pr1 H ;; f) ;; h).
  repeat rewrite <- precategory_assoc.
  apply maponpaths. assumption.
  rewrite (pr2 (pr2 H)).
  rewrite precategory_id_left.
  apply idpath.
Qed.
  
Lemma post_comp_with_iso_is_inj (C : precategory) (b c : precategory_objects C)
     (h : b --> c) (H : is_precat_isomorphism h) 
   (a : precategory_objects C) (f g : a --> b) : f ;; h == g ;; h -> f == g.
Proof.
  intro HH.
  pathvia (f ;; (h ;; pr1 H)).
  rewrite (pr1 (pr2 H)).
  rewrite precategory_id_right.
  apply idpath.
  pathvia (g ;; (h ;; pr1 H)).
  repeat rewrite precategory_assoc.
  rewrite HH. apply idpath.
  rewrite (pr1 (pr2 H)).
  rewrite precategory_id_right.
  apply idpath.
Qed.

(** ** Saturated precategories *)

Definition precat_paths_to_iso {C : precategory} (a b : precategory_objects C):
      a == b -> iso_precat a b.
Proof.
  intro H.
  destruct H.
  exact (identity_iso_precat a).
Defined.
      
Notation idtoiso := (precat_paths_to_iso _ _ ).

Definition is_saturated (C : precategory) := forall (a b : precategory_objects C),
    isweq (precat_paths_to_iso a b).

Lemma isaprop_is_saturated (C : precategory) : isaprop (is_saturated C).
Proof.
  apply impred.
  intro a.
  apply impred.
  intro b.
  apply isapropisweq.
Qed.

Definition sat_precat := total2 (fun C : precategory => is_saturated C).

Definition precat_from_sat_precat (C : sat_precat) : precategory := pr1 C.
Coercion precat_from_sat_precat : sat_precat >-> precategory.

Lemma satcat_has_groupoid_ob (C : sat_precat) : 
  isofhlevel 3 (precategory_objects C).
Proof.
  apply isofhlevelonestep.
  intros a b.
  apply (isofhlevelweqb _ (tpair _ _ (pr2 C a b))).
  apply isaset_iso_precat.
Qed.
  
Definition isotoid (C : precategory) (H : is_saturated C) {a b : precategory_objects C}:
      iso_precat a b -> a == b := invmap (weqpair _ (H a b)).

Lemma idtoiso_isotoid (C : precategory) (H : is_saturated C) (a b : precategory_objects C)
    (f : iso_precat a b) : idtoiso (isotoid _ H f) == f.
Proof.
  unfold isotoid.
  set (Hw := homotweqinvweq (weqpair idtoiso (H a b))).
  simpl in Hw.
  rewrite Hw.
  apply idpath.
Qed.

Lemma isotoid_idtoiso (C : precategory) (H : is_saturated C) (a b : precategory_objects C)
    (p : a == b) : isotoid _ H (idtoiso p) == p.
Proof.
  unfold isotoid.
  set (Hw := homotinvweqweq (weqpair idtoiso (H a b))).
  simpl in Hw.
  rewrite Hw.
  apply idpath.
Qed.


(* not needed, presumably *)
Definition double_transport' {C : precategory} {a a' b b' : precategory_objects C}
   (p : a == a') (q : b == b') (f : a --> b) : a' --> b'.
Proof.
  induction p.
  induction q.
  exact f.
Defined.

Definition double_transport {C : precategory} {a a' b b' : precategory_objects C}
   (p : a == a') (q : b == b') (f : a --> b) : a' --> b' :=
  transportf (fun TT => a' --> TT) q (transportf (fun SS => SS --> b) p f).

Lemma idtoiso_postcompose (C : precategory) (a b b' : precategory_objects C)
  (p : b == b') (f : a --> b) :
      f ;; idtoiso p == transportf (fun b => a --> b) p f.
Proof.
  induction p.
  simpl.
  rewrite precategory_id_right.
  apply idpath.
Qed.

Lemma idtoiso_postcompose_iso (C : precategory) (a b b' : precategory_objects C)
  (p : b == b') (f : iso_precat a b) : 
    iso_comp f (idtoiso p) == transportf (fun b => iso_precat a b) p f.
Proof.
  induction p.
  apply eq_iso_precat.
  simpl.
  rewrite transportf_idpath.
  apply precategory_id_right.
Qed.


Lemma idtoiso_precompose (C : precategory) (a a' b : precategory_objects C)
  (p : a == a') (f : a --> b) : 
      (idtoiso (!p)) ;; f == transportf (fun a => a --> b) p f.
Proof.
  induction p.
  simpl.
  rewrite transportf_idpath.
  apply precategory_id_left.
Qed.

Lemma double_transport_idtoiso (C : precategory) (a a' b b' : precategory_objects C) 
  (p : a == a') (q : b == b')  (f : a --> b) : 
  double_transport p q f == inv_from_iso (idtoiso p) ;; f ;; idtoiso q.
Proof.
  induction p.
  induction q.
  simpl.
  rewrite precategory_id_right.
  unfold inv_from_iso.
  simpl.
  rewrite precategory_id_left.
  apply idpath.
Qed.

Lemma idtoiso_inv (C : precategory) (a a' : precategory_objects C)
  (p : a == a') : idtoiso (!p) == iso_inv_from_iso (idtoiso p).
Proof.
  induction p.
  apply eq_iso_precat. 
  simpl.
  unfold inv_from_iso.
  simpl.
  apply idpath.
Qed.


Lemma idtoiso_concat (C : precategory) (a a' a'' : precategory_objects C)
  (p : a == a') (q : a' == a'') :
  idtoiso (p @ q) == iso_comp (idtoiso p) (idtoiso q).
Proof.
  induction p.
  induction q.
  simpl.
  apply eq_iso_precat.
  simpl.
  rewrite precategory_id_left.
  apply idpath.
Qed.


Lemma idtoiso_inj (C : precategory) (H : is_saturated C) (a a' : precategory_objects C)
   (p p' : a == a') : idtoiso p == idtoiso p' -> p == p'.
Proof.
  intro H'.
  set (H'' := maponpaths (isotoid _ H )  H').
  repeat rewrite isotoid_idtoiso in H''.
  assumption.
Qed.

Lemma isotoid_inj (C : precategory) (H : is_saturated C) (a a' : precategory_objects C)
   (f f' : iso_precat a a') : isotoid _ H f == isotoid _ H f' -> f == f'.
Proof.
  intro H'.
  set (H'' := maponpaths idtoiso H').
  repeat rewrite idtoiso_isotoid in H''.
  assumption.
Qed.


Lemma isotoid_comp (C : precategory) (H : is_saturated C) (a b c : precategory_objects C)
  (e : iso_precat a b) (f : iso_precat b c) :
  isotoid _ H (iso_comp e f) == isotoid _ H e @ isotoid _ H f.
Proof.
  apply idtoiso_inj.
    assumption.
  rewrite idtoiso_concat.
  repeat rewrite idtoiso_isotoid.
  apply idpath.
Qed.

