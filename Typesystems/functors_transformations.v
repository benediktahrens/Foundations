(************************************************************

Benedikt Ahrens and Chris Kapulkin
january 2013


************************************************************)


(************************************************************

Contents :  

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

Require Import precategories.

Notation "a == b" := (paths a b) (at level 70, no associativity).
Notation "! p " := (pathsinv0 p) (at level 50).
Notation "p @ q" := (pathscomp0 p q) (at level 60, right associativity).

Local Notation "a --> b" := (precategory_morphisms a b)(at level 50).
Local Notation "f ;; g" := (precategory_compose f g)(at level 50).

Ltac pathvia b := (apply (@pathscomp0 _ _ b _ )).




(** * Functors : Morphisms of precategories *)


Definition precategory_ob_mor_fun (C C' : precategory_ob_mor) := total2 (
    fun F : precategory_objects C -> precategory_objects C' => 
             forall a b : precategory_objects C, a --> b -> F a --> F b).

Definition precategory_ob_mor_fun_objects {C C' : precategory_ob_mor}
     (F : precategory_ob_mor_fun C C') : 
   precategory_objects C -> precategory_objects C' := pr1 F.
Coercion precategory_ob_mor_fun_objects : precategory_ob_mor_fun >-> Funclass.


Definition precategory_ob_mor_fun_morphisms {C C' : precategory_ob_mor}
     (F : precategory_ob_mor_fun C C') { a b : precategory_objects C} : 
       a --> b -> F a --> F b := pr2 F a b.

Local Notation "# F" := (precategory_ob_mor_fun_morphisms F)(at level 3).


Definition is_precategory_fun {C C' : precategory_data} 
         (F : precategory_ob_mor_fun C C') :=
     dirprod (forall a : precategory_objects C, 
                 #F (precategory_identity a) == precategory_identity (F a))
             (forall a b c : precategory_objects C, forall f : a --> b,
                 forall g : b --> c, 
                #F (f ;; g) == #F f ;; #F g).

Lemma isaprop_is_precategory_fun (C C' : precategory_data) 
       (F : precategory_ob_mor_fun C C'):
  isaprop (is_precategory_fun F).
Proof.
  apply isofhleveldirprod.
  apply impred; intro a.
  apply (precategory_morphisms (C:=C')).
  apply impred; intro a.
  apply impred; intro b.
  apply impred; intro c.
  apply impred; intro f.
  apply impred; intro g.
  apply (precategory_morphisms (C:=C')).
Qed.

Definition precategory_fun (C C' : precategory_data) := total2 (
   fun F : precategory_ob_mor_fun C C' => 
      is_precategory_fun  F).

Lemma precategory_fun_eq (C C' : precategory_data) (F F': precategory_fun C C'):
    pr1 F == pr1 F' -> F == F'.
Proof.
  intro H.
  apply (total2_paths H).
  apply proofirrelevance.
  apply isaprop_is_precategory_fun.
Defined.

Definition precategory_ob_mor_fun_from_precategory_fun (C C': precategory_data)
     (F : precategory_fun C C') : precategory_ob_mor_fun C C' := pr1 F.
Coercion precategory_ob_mor_fun_from_precategory_fun : precategory_fun >->
      precategory_ob_mor_fun.


Definition precategory_fun_eq_eq_from_precategory_fun_ob_eq (C C' : precategory_data)
   (F G : precategory_fun C C') (p q : F == G) 
   (H : base_paths _ _ (base_paths _ _  p) == 
         base_paths _ _ (base_paths _ _ q)) :
    p == q.
Proof.
  apply equal_equalities_between_pairs.
  simpl.
  assert (H' : base_paths _ _ p == base_paths _ _ q).
  apply equal_equalities_between_pairs.
  simpl. 
  apply (@total2_paths2 _ (fun p : pr1 (pr1 F) == pr1 (pr1 G) =>
          transportf
            (fun x : precategory_objects C -> precategory_objects C' =>
            (fun x0 : precategory_objects C -> precategory_objects C' => 
            forall a b : precategory_objects C, a --> b -> x0 a --> x0 b) x)
            p (pr2 (pr1 F)) == pr2 (pr1 G)) _ 
   (fiber_path_fibr (base_paths F G p)) _ (fiber_path_fibr (base_paths F G q))  H).
   apply uip.
   change (isaset) with (isofhlevel 2).
   apply impred.
   intro a.
   apply impred.
   intro b.
   apply impred.
   intro f.
   apply (pr1 (pr1 G ) a --> pr1 (pr1 G) b).
   apply (@total2_paths2 (pr1 F == pr1 G)  
    (fun x : pr1 F == pr1 G => transportf _ x (pr2 F) == pr2 G)
          (base_paths F G p) (fiber_path_fibr p) (base_paths F G q) (fiber_path_fibr q) H').
   apply uip.
   apply isasetaprop.
   apply isaprop_is_precategory_fun.
Defined.


(*
Definition precategory_fun_eq_eq_from_precategory_fun_ob_eq (C C' : precategory_data)
   (F G : precategory_fun C C') (p q : F == G) 
   (H : precategory_fun_ob_eq_from_precategory_fun_eq _ _ _ _ p == 
         precategory_fun_ob_eq_from_precategory_fun_eq _ _ _ _ q) :
    p == q.
Proof.
  assert (H' : base_paths _ _ p == base_paths _ _ q).
  unfold base_paths.
  unfold precategory_fun_ob_eq_from_precategory_fun_eq in H.
  unfold base_paths in H.
  simpl in *.
  apply (total2_paths H).
  simpl.
*)
  

Definition precategory_fun_id (C C' : precategory_data)(F : precategory_fun C C'):
       forall a : precategory_objects C, 
                 #F (precategory_identity a) == precategory_identity (F a) :=
     pr1 (pr2 F).

Definition precategory_fun_comp (C C' : precategory_data)
      (F : precategory_fun C C'):
       forall a b c : precategory_objects C, forall f : a --> b,
                 forall g : b --> c, 
                #F (f ;; g) == #F f ;; #F g := pr2 (pr2 F).

(** *** Functors preserve isomorphisms *)

Lemma precategory_fun_on_iso_is_iso (C C' : precategory) (F : precategory_fun C C')
    (a b : precategory_objects C)(f : iso_precat a b) :
       is_precat_isomorphism (#F f).
Proof.
  exists (#F (inv_from_iso f)).
  simpl; split; simpl.
  rewrite <- precategory_fun_comp.
  rewrite iso_inv_after_iso.
  apply precategory_fun_id.
  
  rewrite <- precategory_fun_comp.
  rewrite (iso_after_iso_inv _ _ _ f).
  apply precategory_fun_id.
Qed.


Definition precategory_fun_on_iso (C C' : precategory) (F : precategory_fun C C')
    (a b : precategory_objects C)(f : iso_precat a b) : iso_precat (F a) (F b).
Proof.
  exists (#F f).
  apply precategory_fun_on_iso_is_iso.
Defined.
 
Lemma precategory_fun_on_iso_inv (C C' : precategory) (F : precategory_fun C C')
    (a b : precategory_objects C) (f : iso_precat a b) : 
   precategory_fun_on_iso _ _ F _ _ (iso_inv_from_iso f) == 
       iso_inv_from_iso (precategory_fun_on_iso _ _ F _ _ f).
Proof.
  apply inv_iso_unique.
  simpl.
  split; simpl.
  rewrite <- precategory_fun_comp.
  rewrite iso_inv_after_iso.
  apply precategory_fun_id.
  rewrite <- precategory_fun_comp.
  rewrite iso_after_iso_inv.
  apply precategory_fun_id.
Qed.
  
(** *** Functors preserve inverses *)

Lemma precategory_fun_on_inv_from_iso (C C' : precategory) (F : precategory_fun C C')
    (a b : precategory_objects C)(f : iso_precat a b) :
      #F (inv_from_iso f) == inv_from_iso (precategory_fun_on_iso _ _ F _ _ f) .
Proof.
  set (H := precategory_fun_on_iso_inv _ _ F _ _ f).
  set (H' := base_paths _ _ H). simpl in *.
  apply H'.
Qed. 


(** *** Fully faithful functors *)

Definition fully_faithful {C D : precategory} (F : precategory_fun C D) := 
  forall a b : precategory_objects C, 
    isweq (precategory_ob_mor_fun_morphisms F (a:=a) (b:=b)).

Lemma isaprop_fully_faithful (C D : precategory) (F : precategory_fun C D) :
   isaprop (fully_faithful F).
Proof.
  apply impred; intro a.
  apply impred; intro b.
  apply isapropisweq.
Qed.

Definition weq_from_fully_faithful (C D : precategory) (F : precategory_fun C D) 
      (HF : fully_faithful F) (a b : precategory_objects C) : 
   weq (a --> b) (F a --> F b).
Proof.
  exists (precategory_ob_mor_fun_morphisms F (a:=a) (b:=b)).
  exact (HF a b).
Defined.


Definition fully_faithful_inv_hom (C D : precategory) (F : precategory_fun C D) 
      (HF : fully_faithful F) (a b : precategory_objects C) :
      F a --> F b -> a --> b :=
 invweq (weq_from_fully_faithful C D F HF a b).

Lemma fully_faithful_inv_identity (C D : precategory) (F : precategory_fun C D)
      (HF : fully_faithful F) (a : precategory_objects C) : 
    fully_faithful_inv_hom _ _ _ HF _ _ (precategory_identity (F a)) ==
         precategory_identity _ .
Proof.
  set (h' := equal_transport_along_weq _ _ (weq_from_fully_faithful _ _ _ HF a a)).
  apply h'.
  set (HFFaa := homotweqinvweq (weq_from_fully_faithful _ _ _ HF a a)
                 (precategory_identity _ )).
  unfold fully_faithful_inv_hom.
  simpl in *.
  rewrite HFFaa.
  rewrite precategory_fun_id; apply idpath.
Qed.


Lemma fully_faithful_inv_comp (C D : precategory) (F : precategory_fun C D)
      (HF : fully_faithful F) (a b c : precategory_objects C) 
      (f : F a --> F b) (g : F b --> F c) : 
    fully_faithful_inv_hom _ _ _ HF _ _ (f ;; g) ==
       fully_faithful_inv_hom _ _ _ HF _ _ f ;; 
           fully_faithful_inv_hom _ _ _ HF _ _ g.
Proof.
  set (h' := equal_transport_along_weq _ _ (weq_from_fully_faithful _ _ _ HF a c)).
  apply h'.
  set (HFFac := homotweqinvweq (weq_from_fully_faithful _ _ _ HF a c)
                 (f ;; g)).
  unfold fully_faithful_inv_hom.
  simpl in *.
  rewrite HFFac.
  rewrite precategory_fun_comp.
  set (HFFab := homotweqinvweq (weq_from_fully_faithful _ _ _ HF a b) f).
  set (HFFbc := homotweqinvweq (weq_from_fully_faithful _ _ _ HF b c) g).
  simpl in *.
  rewrite HFFab.
  rewrite HFFbc.
  apply idpath.
Qed.



(** Fully faithful functors reflect isos *)

Lemma fully_faithful_reflects_iso_proof (C D : precategory)(F : precategory_fun C D) 
        (HF : fully_faithful F)
    (a b : precategory_objects C) (f : iso_precat (F a) (F b)) : 
     is_precat_isomorphism (fully_faithful_inv_hom C D F HF a b f).
Proof.
  exists (fully_faithful_inv_hom C D F HF b a (inv_from_iso f)).
  simpl.
  unfold fully_faithful_inv_hom.
  split.
(*  unfold weq_from_fully_faithful.*)
  set (hhh := equal_transport_along_weq _ _ (weq_from_fully_faithful C D F HF a a)).
  apply hhh.
  set (HFFab := homotweqinvweq (weq_from_fully_faithful C D F HF a b)).
  set (HFFba := homotweqinvweq (weq_from_fully_faithful C D F HF b a)).
  simpl in *.
  rewrite precategory_fun_comp.
  rewrite HFFab.
  rewrite HFFba.
  rewrite precategory_fun_id.
  apply iso_inv_after_iso.
  
  set (hhh := equal_transport_along_weq _ _ (weq_from_fully_faithful C D F HF b b)).
  apply hhh.
  set (HFFab := homotweqinvweq (weq_from_fully_faithful C D F HF a b)).
  set (HFFba := homotweqinvweq (weq_from_fully_faithful C D F HF b a)).
  simpl in *.
  rewrite precategory_fun_comp.
  rewrite HFFab.
  rewrite HFFba.
  rewrite precategory_fun_id.
  set (Hff := pr2 (pr2 (pr2 f))).
  simpl in *.
  unfold inv_from_iso.
  destruct f.
  simpl. assumption.
Qed.

Definition  iso_from_fully_faithful_reflection (C D : precategory)(F : precategory_fun C D) 
        (HF : fully_faithful F)
    (a b : precategory_objects C) (f : iso_precat (F a) (F b)) : 
      iso_precat a b.
Proof.
  exists (fully_faithful_inv_hom C D F HF a b f).
  apply fully_faithful_reflects_iso_proof.
Defined.

Lemma precategory_fun_on_iso_iso_from_fully_faithful_reflection (C D : precategory)
      (F : precategory_fun C D) (HF : fully_faithful F) (a b : precategory_objects C)
   (f : iso_precat (F a) (F b)) :
      precategory_fun_on_iso _ _  F a b
        (iso_from_fully_faithful_reflection _ _  F HF a b f) == f.
Proof.
  apply eq_iso_precat.
  simpl.
  set (H3 := homotweqinvweq (weq_from_fully_faithful _ _ _ HF a b)).
  simpl in H3.
  unfold fully_faithful_inv_hom. simpl.
  rewrite H3.
  apply idpath.
Qed.



(** *** Essentially surjective functors *)

Definition essentially_surjective {C D : precategory} (F : precategory_fun C D) :=
  forall b, ishinh (total2 (fun a => iso_precat (F a) b)).
   
(** *** Faithful functors *)

Definition faithful {C D : precategory} (F : precategory_fun C D) := 
  forall a b : precategory_objects C, forall f g : a --> b,
       #F f == #F g -> f == g.

Lemma isaprop_faithful (C D : precategory) (F : precategory_fun C D) : 
   isaprop (faithful F).
Proof.
  apply impred; intro c.
  apply impred; intro b.
  apply impred; intro f.
  apply impred; intro g.
  apply impred; intro H.
  apply (pr2 (c --> b)).
Qed.

(** *** Full functors *)

Definition full {C D : precategory} (F : precategory_fun C D) :=
   forall a b (g : F a --> F b), total2 (fun f : a --> b => #F f == g).





(** *** Fully faithful is the same as full and faithful *)

Definition full_and_faithful {C D : precategory} (F : precategory_fun C D) :=
   dirprod (full F) (faithful F).



Lemma fully_faithful_implies_full_and_faithful (C D : precategory) (F : precategory_fun C D) :
   fully_faithful F -> full_and_faithful F.
Proof.
  intro H.
  split; simpl.
  unfold full. 
  intros a b f.
  exists (fully_faithful_inv_hom _ _ _ H _ _ f).
  set (HFFaa := homotweqinvweq (weq_from_fully_faithful _ _ _ H a b)).
  simpl in HFFaa.
  apply HFFaa.
  
  unfold faithful.
  intros a b f g Heq.
  apply (equal_transport_along_weq _ _ (weq_from_fully_faithful C D F H a b)).
  simpl. assumption.
Qed.

Lemma full_and_faithful_implies_fully_faithful (C D : precategory) (F : precategory_fun C D) :
   full_and_faithful F -> fully_faithful F.
Proof. 
  intros [Hfull Hfaith].
  intros a b g.
  unfold full in Hfull.
  exists (Hfull a b g).
  unfold hfiber.
  intro t.
  unfold faithful in Hfaith.
  assert (X : pr1 t == pr1 (Hfull a b g)).
  apply Hfaith.
  rewrite (pr2 t). 
  set (H':= pr2 (Hfull a b g)).
  simpl in H'.
  rewrite H'. apply idpath.
  simpl in *.
  apply (total2_paths  X).
  apply proofirrelevance.
  apply (pr2 (F a --> F b)).
Qed.
 
Lemma isaprop_full_and_faithful (C D : precategory) (F : precategory_fun C D) :
   isaprop (full_and_faithful F).
Proof.
  apply isofhlevelsn.
  intro H.
  apply isofhleveldirprod.
  apply impred; intro b.
  apply impred; intro c.
  apply impred; intro g.
  apply invproofirrelevance.
  intros f f'.
  assert (HH : pr1 f == pr1 f').
  
  set (HF := full_and_faithful_implies_fully_faithful _ _ _ H).
  set (h' := equal_transport_along_weq _ _
          (weq_from_fully_faithful _ _ _ HF b c)).
       apply h'.
       simpl.
  rewrite (pr2 f).
  rewrite (pr2 f').
  apply idpath.
  
  apply (total2_paths HH).
  apply proofirrelevance.
  apply (pr2 (F b --> F c)).
  
  apply isaprop_faithful.
Qed.
  
  
Definition weq_fully_faithful_full_and_faithful (C D : precategory) (F : precategory_fun C D) :
   weq (fully_faithful F) (full_and_faithful F) :=
  weqimplimpl (fully_faithful_implies_full_and_faithful _ _ F)
              (full_and_faithful_implies_fully_faithful _ _ F)
              (isaprop_fully_faithful _ _ F)
              (isaprop_full_and_faithful _ _ F).

(** ** Image on objects of a functor  *)
(** is used later to define the full image subcategory of a category [D] 
       defined by a functor [F : C -> D] *)

Definition is_in_img_precategory_fun {C D : precategory} (F : precategory_fun C D) 
      (d : precategory_objects D) :=
  ishinh (
  total2 (fun c : precategory_objects C => iso_precat (F c) d)).

Definition sub_img_precategory_fun {C D : precategory}(F : precategory_fun C D) :
    hsubtypes (precategory_objects D) := 
       fun d : precategory_objects D => is_in_img_precategory_fun F d.



(** ** Composition of Functors, Identity Functors *)

(** *** Composition *)
Lemma precategory_fun_composite_ob_mor {C C' C'' : precategory}
       (F : precategory_fun C C') (F' : precategory_fun C' C'') :
 is_precategory_fun  
  (tpair (fun F : precategory_objects C -> precategory_objects C'' => 
             forall a b : precategory_objects C, a --> b -> F a --> F b) 
    (fun a => F' (F a))
               (fun (a b : precategory_objects C) f => #F' (#F f))).
Proof.
  split;
  simpl.
  intro a.
  rewrite precategory_fun_id.
  rewrite precategory_fun_id.
  apply (idpath _).
  
  intros a b c f g.
  rewrite precategory_fun_comp.
  rewrite precategory_fun_comp.
  apply idpath.
Qed.

Definition precategory_fun_composite (C C' C'' : precategory)
       (F : precategory_fun C C') (F' : precategory_fun C' C'') :
  precategory_fun C C'' := tpair _ _ (precategory_fun_composite_ob_mor F F').

(** *** Identity functor *)

Lemma precategory_fun_identity_ob_mor (C : precategory) :
 is_precategory_fun  
  (tpair (fun F : precategory_objects C -> precategory_objects C => 
             forall a b : precategory_objects C, a --> b -> F a --> F b) 
    (fun a => a)
               (fun (a b : precategory_objects C) f => f)).
Proof.
  split;
  simpl.
  intro a.
  apply (idpath _).
  
  intros a b c f g.
  apply idpath.
Qed.

Definition precategory_fun_identity (C : precategory) :
     precategory_fun C  C.
Proof.
  exists (tpair (fun F : precategory_objects C -> precategory_objects C => 
             forall a b : precategory_objects C, a --> b -> F a --> F b) 
    (fun a => a)
               (fun (a b : precategory_objects C) f => f)).
  apply  (precategory_fun_identity_ob_mor C).
Defined.


    
(** ** Precategories in style of essentially algebraic cats *)
(** Of course we later want SETS of objects, rather than types,
    but the construction can already be specified.
*)
       
Definition precategory_total_morphisms (C : precategory_ob_mor) := total2 (
   fun ab : dirprod (precategory_objects C)(precategory_objects C) =>
        precategory_morphisms (pr1 ab) (pr2 ab)).

Lemma isaset_setcategory_total_morphisms (C : setcategory) : 
   isaset (precategory_total_morphisms C).
Proof.
  change isaset with (isofhlevel 2).
  apply isofhleveltotal2.
  apply isofhleveldirprod;
  apply C.
  exact (fun x => (pr2 (pr1 x --> pr2 x))).
Qed.

Definition setcategory_total_morphisms_set (C : setcategory) : hSet :=
    hSetpair _ (isaset_setcategory_total_morphisms C).

Definition precategory_source (C : precategory_ob_mor) : 
     precategory_total_morphisms C -> precategory_objects C := 
     fun abf => pr1 (pr1 abf).

Definition precategory_target (C : precategory_ob_mor) : 
     precategory_total_morphisms C -> precategory_objects C := 
     fun abf => pr2 (pr1 abf).

Definition precategory_total_id (C : precategory_data) : 
      precategory_objects C -> precategory_total_morphisms C :=
      fun c => tpair _ (dirprodpair c c) (precategory_identity c).

Definition precategory_total_comp'' (C : precategory_data) : 
      forall f g : precategory_total_morphisms C,
        precategory_target C f == precategory_source C g ->
         precategory_total_morphisms C.
Proof.
  intros f g H.
  destruct f as [[a b] f]. simpl in *.
  destruct g as [[b' c] g]. simpl in *.
  unfold precategory_target in H; simpl in H.
  unfold precategory_source in H; simpl in H. 
  simpl.
  exists (dirprodpair a c). simpl.
  exact ((f ;; precategory_eq_morphism C b b' H) ;; g).
Defined.

Definition precategory_total_comp (C : precategory_data) : 
      forall f g : precategory_total_morphisms C,
        precategory_target C f == precategory_source C g ->
         precategory_total_morphisms C := 
  fun f g H => 
     tpair _ (dirprodpair (pr1 (pr1 f))(pr2 (pr1 g)))
        ((pr2 f ;; precategory_eq_morphism _ _ _ H) ;; pr2 g).



(** * Natural transformations *)

(*
Definition precategory_fun_fun_data {C C' : precategory_data}
  (F F' : precategory_ob_mor_fun C C') :=
     forall x : precategory_objects C, F x --> F' x.
*)
Definition is_precategory_fun_fun {C C' : precategory_data}
  (F F' : precategory_ob_mor_fun C C')
  (t : forall x : precategory_objects C, F x -->  F' x) := 
  forall (x x' : precategory_objects C)(f : x --> x'),
    #F f ;; t x' == t x ;; #F' f.


Lemma isaprop_is_precategory_fun_fun {C C' : precategory_data}
  (F F' : precategory_ob_mor_fun C C') (t : forall x : precategory_objects C, F x -->  F' x):
  isaprop (is_precategory_fun_fun F F' t).
Proof.
  apply impred; intro x.
  apply impred; intro x'.
  apply impred; intro f.
  apply (precategory_morphisms (C:=C')).
Qed.


Definition precategory_fun_fun {C C' : precategory_data}
  (F F' : precategory_ob_mor_fun C C') := total2 (
   fun t : forall x : precategory_objects C, F x -->  F' x => 
         is_precategory_fun_fun F F' t).

Lemma isaset_precategory_fun_fun {C C' : precategory_data}
  (F F' : precategory_ob_mor_fun C C') : isaset
    (precategory_fun_fun F F').
Proof.
  change isaset with (isofhlevel 2).
  apply isofhleveltotal2.
  apply impred.
  intro t. apply (F t --> F' t).
  intro x. 
  apply isasetaprop.
  apply isaprop_is_precategory_fun_fun.
Qed.

Definition precategory_fun_fun_carrier (C C' : precategory_data)
 (F F' : precategory_ob_mor_fun C C')(a : precategory_fun_fun F F') :
   forall x : precategory_objects C, F x --> F' x := pr1 a.
Coercion precategory_fun_fun_carrier : precategory_fun_fun >-> Funclass.

Definition precategory_fun_fun_ax {C C' : precategory_data}
  (F F' : precategory_ob_mor_fun C C') (a : precategory_fun_fun F F') :
  forall (x x' : precategory_objects C)(f : x --> x'),
    #F f ;; a x' == a x ;; #F' f := pr2 a.

(** Equality between two natural transformations *)

Lemma precategory_fun_fun_eq {C C' : precategory_data}
  (F F' : precategory_ob_mor_fun C C')(a a' : precategory_fun_fun F F'):
  (forall x, a x == a' x) -> a == a'.
Proof.
  intro H.
  assert (H' : pr1 a == pr1 a').
  apply dep_funextfunax.
  assumption.
  apply (total2_paths H').
  apply proofirrelevance.
  apply isaprop_is_precategory_fun_fun.
Qed.

Definition precategory_fun_fun_eq_pointwise (C C' : precategory_data)
   (F F' : precategory_ob_mor_fun C C') (a a' : precategory_fun_fun F F'):
      a == a' -> forall x, a x == a' x.
Proof.
  intro h.
  apply toforallpaths.
  apply maponpaths.
  assumption.
Qed.


(** ** Functor category (C,C') *)

Definition precategory_fun_fun_precategory_ob_mor (C C' : precategory_data): 
  precategory_ob_mor := precategory_ob_mor_pair 
   (precategory_fun C C') (fun F F' : precategory_fun C C' =>
                              hSetpair (precategory_fun_fun F F') 
                                       (isaset_precategory_fun_fun F F')).

(** *** Identity natural transformation *)

Lemma is_precategory_fun_fun_id {C C' : precategory}
  (F : precategory_ob_mor_fun C C') : is_precategory_fun_fun F F
     (fun c : precategory_objects C => precategory_identity (F c)).
Proof.
  intros c c' f.
  rewrite precategory_id_left.
  rewrite precategory_id_right.
  apply idpath.
Qed.

Definition precategory_fun_fun_id {C C' : precategory}
  (F : precategory_ob_mor_fun C C') : precategory_fun_fun F F :=
    tpair _ _ (is_precategory_fun_fun_id F).

(** *** Composition of natural transformations *)

Lemma is_precategory_fun_fun_comp {C C' : precategory}
  {F G H : precategory_ob_mor_fun C C'}
  (a : precategory_fun_fun F G)
  (b : precategory_fun_fun G H): is_precategory_fun_fun F H
     (fun x : precategory_objects C => a x ;; b x).
Proof.
  intros c c' f.
  rewrite precategory_assoc.
  rewrite precategory_fun_fun_ax.
  rewrite <- precategory_assoc.
  rewrite precategory_fun_fun_ax.
  apply precategory_assoc.
Qed.


Definition precategory_fun_fun_comp {C C' : precategory}
  (F G H: precategory_ob_mor_fun C C') 
  (a : precategory_fun_fun F G)
  (b : precategory_fun_fun G H): precategory_fun_fun F H :=
    tpair _ _ (is_precategory_fun_fun_comp a b).


(** *** The data of the functor precategory *)

Definition precategory_fun_precategory_data (C C' : precategory): 
 precategory_data.
Proof.
  apply ( precategory_data_pair 
        (precategory_fun_fun_precategory_ob_mor C C')).
  intro a. simpl.
  apply (precategory_fun_fun_id (pr1 a)).
  intros a b c f g.
  apply (precategory_fun_fun_comp _ _ _ f g).
Defined.

(** *** Above data forms a precategory *)

Lemma is_precategory_precategory_fun_precategory_data (C C' : precategory) :
   is_precategory (precategory_fun_precategory_data C C').
Proof.
  repeat split; simpl; intros.
  unfold precategory_identity.
  simpl.
  apply precategory_fun_fun_eq.
  intro x; simpl.
  apply (precategory_id_left).
  
  apply precategory_fun_fun_eq.
  intro x; simpl.
  apply (precategory_id_right).
  
  apply precategory_fun_fun_eq.
  intro x; simpl.
  apply (precategory_assoc).
Qed.

Definition precategory_fun_precategory (C C' : precategory): precategory := 
  tpair _ _ (is_precategory_precategory_fun_precategory_data C C').

Notation "[ C , D ]" := (precategory_fun_precategory C D).

Lemma precategory_fun_fun_comp_pointwise (C C' : precategory)
  (F G H : precategory_objects [C, C']) (A : F --> G) (A' : G --> H) 
   (B : F --> H) : A ;; A' == B -> 
        forall a, pr1 A a ;; pr1 A' a == pr1 B a.
Proof.
  intros H' a.
(*  simpl in *. *)
  pathvia (pr1 (A ;; A') a).
  apply idpath.
  induction H'.
  apply idpath.
Defined.
  
  

(** Characterizing isomorphisms in the functor category *)

Lemma is_precategory_fun_fun_inv_from_pointwise_inv (C D : precategory)
  (F G : precategory_objects [C,D]) (A : F --> G) 
  (H : forall a : precategory_objects C, is_precat_isomorphism (pr1 A a)) :
  is_precategory_fun_fun _ _ 
     (fun a : precategory_objects C => inv_from_iso (tpair _ _ (H a))).
Proof.
  unfold is_precategory_fun_fun.
  intros x x' f.
  apply pathsinv0.
  apply iso_inv_on_right.
  rewrite precategory_assoc.
  apply iso_inv_on_left.
  set (HA:= pr2 A).
  simpl in *.
  unfold is_precategory_fun_fun in HA.
  rewrite HA.
  apply idpath.
Qed.

Definition precategory_fun_fun_inv_from_pointwise_inv (C D : precategory)
  (F G : precategory_objects [C,D]) (A : F --> G) 
  (H : forall a : precategory_objects C, is_precat_isomorphism (pr1 A a)) :
    G --> F := tpair _ _ (is_precategory_fun_fun_inv_from_pointwise_inv _ _ _ _ _ H).


Lemma precategory_fun_iso_if_pointwise_iso (C C' : precategory)
 (F G : precategory_objects [C, C']) (A : F --> G) : 
   (forall a : precategory_objects C, is_precat_isomorphism (pr1 A a)) ->  
           is_precat_isomorphism A .
Proof.
  intro H.
  simpl in *.
  exists (precategory_fun_fun_inv_from_pointwise_inv _ _ _ _ _ H).
  simpl; split; simpl.
  apply precategory_fun_fun_eq.
  intro x; simpl.
  apply (H).
  apply precategory_fun_fun_eq.
  intro x; simpl.
  apply (H).
Qed.  

Definition precategory_fun_iso_from_pointwise_iso (C C' : precategory)
 (F G : precategory_objects [C, C']) (A : F --> G) 
   (H : forall a : precategory_objects C, is_precat_isomorphism (pr1 A a)) : 
     iso_precat F G := 
 tpair _ _ (precategory_fun_iso_if_pointwise_iso _ _ _ _ _  H).


Lemma is_precategory_fun_iso_pointwise_if_iso (C C' : precategory)
 (F G : precategory_objects [C, C']) (A : F --> G) : 
  is_precat_isomorphism A -> 
       forall a : precategory_objects C, is_precat_isomorphism (pr1 A a).  
Proof.
  intros H a.
  simpl in *.
  set (R := pr1 H).
  simpl in *.
  exists (R a).
(*  exists (pr1 H a).
  destruct H as [A' [H1 H2]].
  simpl in A'. exists (A' a).
*)
  unfold is_inverse_in_precat in *; simpl; split.
  set (H1' := precategory_fun_fun_eq_pointwise _ _ _ _ _ _ (pr1 (pr2 H))).
  simpl in H1'.
  apply H1'.
  apply (precategory_fun_fun_eq_pointwise _ _ _ _ _ _ (pr2 (pr2 H))).
Defined.


Definition precategory_fun_iso_pointwise_if_iso (C C' : precategory)
 (F G : precategory_objects [C, C']) (A : F --> G) 
  (H : is_precat_isomorphism A) : 
     forall a : precategory_objects C, 
       iso_precat (pr1 F a) (pr1 G a) := 
  fun a => tpair _ _ (is_precategory_fun_iso_pointwise_if_iso C C' F G A H a).
 
(*
Lemma precategory_fun_iso_pointwise_if_iso_on_idtoiso (C C' : precategory)
  (F G : precategory_objects [C, C']) (A : F == G) :
    forall a : precategory_objects C,
   precategory_fun_iso_pointwise_if_iso C C' F G (idtoiso F) a
    ==  toforallpaths 
  *)  

Definition pr1_pr1_functor_eq_from_functor_iso (C D : precategory)
    (H : is_saturated D) (F G : precategory_objects [C , D]) :
   iso_precat F G -> pr1 (pr1 F) == pr1 (pr1 G).
Proof.
  intro A.
  apply funextsec.
  intro t.
  apply isotoid.
  assumption.
  apply (precategory_fun_iso_pointwise_if_iso _ _ _ _ A).
  apply A.
Defined.




Lemma transport_of_functor_map_is_pointwise (C D : precategory) 
      (F0 G0 : precategory_objects C -> precategory_objects D)
    (F1 : forall a b : precategory_objects C, a --> b -> F0 a --> F0 b)
   (gamma : F0  == G0 ) 
    (a b : precategory_objects C) (f : a --> b) :
transportf (fun x : precategory_objects C -> precategory_objects D => 
            forall a0 b0 : precategory_objects  C, a0 --> b0 -> x a0 --> x b0)
           gamma  F1 a b f == 
transportf (fun TT : precategory_objects D => G0 a --> TT)
  (toforallpaths (fun _ : precategory_objects C => D) F0 G0 gamma b)
  (transportf (fun SS : precategory_objects D => SS --> F0 b)
     (toforallpaths (fun _ : precategory_objects C => D) F0 G0 gamma a) (F1 a b f)).
Proof.
  induction gamma.
  apply idpath.
Defined.


Lemma toforallpaths_funextsec : forall (T : UU) (P : T -> UU) (f g : forall t : T, P t)
          (h : forall t : T, f t == g t), 
            toforallpaths _  _ _ (funextsec _ _ _ h) == h.
Proof.
  intros T P f g h.
  set (H':= homotweqinvweq (weqtoforallpaths _ f g)).
  simpl in H'.
  apply H'.
Qed.


Definition pr1_functor_eq_from_functor_iso (C D : precategory)
    (H : is_saturated D) (F G : precategory_objects [C , D]) :
   iso_precat F G -> pr1 F == pr1 G.
Proof.
  intro A.
  apply (total2_paths (pr1_pr1_functor_eq_from_functor_iso C D H F G A)).
  simpl in *.
  unfold pr1_pr1_functor_eq_from_functor_iso.
  simpl in *.
  apply funextsec.
  intro a.
  apply funextsec.
  intro b.
  apply funextsec.
  intro f.
  rewrite transport_of_functor_map_is_pointwise.
  rewrite toforallpaths_funextsec.
  set (H':= double_transport_idtoiso D _ _ _ _  
         (isotoid D H (precategory_fun_iso_pointwise_if_iso C D F G A (pr2 A) a))
         (isotoid D H (precategory_fun_iso_pointwise_if_iso C D F G A (pr2 A) b))
          (pr2 (pr1 F) a b f)).
          unfold double_transport in H'. 
  pathvia ((inv_from_iso
        (idtoiso
           (isotoid D H
              (precategory_fun_iso_pointwise_if_iso C D F G A (pr2 A) a)));;
      pr2 (pr1 F) a b f);;
     idtoiso
       (isotoid D H
          (precategory_fun_iso_pointwise_if_iso C D F G A (pr2 A) b))).
  apply H'.
  clear H'.
  rewrite idtoiso_isotoid.
  rewrite idtoiso_isotoid.
  destruct A as [A Aiso].
  simpl in *.
  pathvia 
    (inv_from_iso (precategory_fun_iso_pointwise_if_iso C D F G A Aiso a) ;;
       (A a ;; #G f)).
  rewrite <- precategory_assoc.
  apply maponpaths.
  apply (precategory_fun_fun_ax _ _ A).
  rewrite precategory_assoc.

  unfold precategory_fun_iso_pointwise_if_iso.
  unfold inv_from_iso.
  simpl in *.

  destruct Aiso as [A' AH].
  simpl in *.
  destruct AH as [A1 A2].
  rewrite (precategory_fun_fun_comp_pointwise _ _ _ _ _ _ _ _ A2).
  simpl.
  rewrite precategory_id_left.
  apply idpath.
Defined.

Definition functor_eq_from_functor_iso {C D : precategory}
    (H : is_saturated D) (F G : precategory_objects [C , D]) 
    (H' : iso_precat F G) : F == G.
Proof.
  apply (precategory_fun_eq _ _ F G).
  apply pr1_functor_eq_from_functor_iso;
  assumption.
Defined.


Lemma idtoiso_compute_pointwise (C D : precategory) (F G : precategory_objects [C, D])
     (p : F == G) (a : precategory_objects C) :
precategory_fun_iso_pointwise_if_iso C D F G (idtoiso p) (pr2 (idtoiso p)) a ==
idtoiso
  (toforallpaths (fun _ : precategory_objects C => D) (pr1 (pr1 F)) (pr1 (pr1 G))
     (base_paths (pr1 F) (pr1 G) (base_paths F G p)) a).
Proof.
  induction p.
  simpl.
  apply eq_iso_precat. simpl. apply idpath.
Qed.


Lemma functor_eq_from_functor_iso_idtoiso (C D : precategory)
    (H : is_saturated D)
    (F G : precategory_objects [C, D]) (p : F == G) :
  functor_eq_from_functor_iso H F G (idtoiso p) == p.
Proof.
  simpl.
  apply precategory_fun_eq_eq_from_precategory_fun_ob_eq.
  unfold functor_eq_from_functor_iso.
  unfold precategory_fun_eq.
  simpl.
  rewrite base_total_path_fibr.
  unfold pr1_functor_eq_from_functor_iso.
  rewrite base_total_path_fibr.
  unfold pr1_pr1_functor_eq_from_functor_iso.
  
  apply (equal_transport_along_weq _ _   (weqtoforallpaths _ _ _ )).
  
  simpl.
  rewrite toforallpaths_funextsec.
  simpl.
  apply funextsec.
  intro a. 
  rewrite idtoiso_compute_pointwise.
  
  rewrite isotoid_idtoiso.
  apply idpath.
Qed.

Lemma idtoiso_functor_eq_from_functor_iso (C D : precategory)
    (H : is_saturated D)
    (F G : precategory_objects [C, D]) (gamma : iso_precat F G) :
        idtoiso  (functor_eq_from_functor_iso H F G gamma) == gamma.
Proof.
  apply eq_iso_precat.
  simpl.
  apply precategory_fun_fun_eq.
  intro a.
  set (H':= idtoiso_compute_pointwise C D F G (functor_eq_from_functor_iso H F G gamma) a).
  simpl in *.
  set (H2 := maponpaths (@pr1 _ _ ) H').
  simpl in H2.
  pathvia (pr1
       (idtoiso
          (toforallpaths (fun _ : precategory_objects C => D) (pr1 (pr1 F)) (pr1 (pr1 G))
             (base_paths (pr1 F) (pr1 G)
                (base_paths F G (functor_eq_from_functor_iso H F G gamma))) a))).
  apply H2. clear H2.
  unfold functor_eq_from_functor_iso.
  simpl.
  unfold precategory_fun_eq.
  rewrite base_total_path_fibr.
  unfold pr1_functor_eq_from_functor_iso.
  rewrite base_total_path_fibr.

  pathvia (pr1 (idtoiso
     (isotoid D H (precategory_fun_iso_pointwise_if_iso C D F G gamma (pr2 gamma) a)))).
  apply maponpaths.
  apply maponpaths.
  unfold pr1_pr1_functor_eq_from_functor_iso.
  rewrite toforallpaths_funextsec.
  apply idpath.
  rewrite idtoiso_isotoid.
  apply idpath.
Qed.

Lemma isweq_idtoiso_functorcat (C D : precategory) (H : is_saturated D) 
    (F G : precategory_objects [C, D]) :
   isweq (precat_paths_to_iso F G).
Proof.
  apply (gradth _ (functor_eq_from_functor_iso H F G)).
  apply functor_eq_from_functor_iso_idtoiso.
  apply idtoiso_functor_eq_from_functor_iso.
Qed.

Lemma is_saturated_functor_category (C D : precategory) (H : is_saturated D) :
   is_saturated [C, D].
Proof.
  intros F G.
  apply isweq_idtoiso_functorcat.
  apply H.
Qed.


