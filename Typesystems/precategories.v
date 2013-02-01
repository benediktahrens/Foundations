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

Lemma iso_inv_on_right (C : precategory) (a b c: precategory_objects C)
  (f : a --> b) (g : b --> c) (h : a --> c) (H : h == f;;g) (H': is_precat_isomorphism f) :
     inv_from_iso (tpair (is_precat_isomorphism )  f H') ;; h == g.
Proof.
  assert (H2 : inv_from_iso {| pr1 := f; pr2 := H' |};; h == 
                  inv_from_iso {| pr1 := f; pr2 := H' |};; (f ;; g)).
  apply maponpaths; assumption.
  rewrite precategory_assoc in H2.
  destruct H' as [f' [Hf Hf']]. simpl in *.
  unfold inv_from_iso in *;
  simpl in *.
  rewrite Hf' in H2.
  rewrite precategory_id_left in H2.
  assumption.
Qed.

Lemma iso_inv_on_left (C : precategory) (a b c: precategory_objects C)
  (f : a --> b) (g : b --> c) (h : a --> c) (H : h == f;;g) (H': is_precat_isomorphism g) :
     f == h ;; inv_from_iso (tpair is_precat_isomorphism g H').
Proof.
  assert (H2 : h ;; inv_from_iso {| pr1 := g; pr2 := H' |} == 
                         (f;; g) ;; inv_from_iso {| pr1 := g; pr2 := H' |}).
    rewrite H. apply idpath.
  rewrite <- precategory_assoc in H2.
  destruct H' as [g' [Hg Hg']]. simpl in *.
  unfold inv_from_iso in *;
  simpl in *.
  rewrite Hg in H2.
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

(*
Definition precategory_fun_ob_eq_from_precategory_fun_eq (C C' : precategory_data)
   (F G : precategory_fun C C') (H : F == G) : 
      precategory_ob_mor_fun_objects F == precategory_ob_mor_fun_objects G.
Proof.
  apply (base_paths _ _ (base_paths _ _ H)).
Defined.
*)

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
(*  Check (total_paths_equiv_fibr
   (fun x : precategory_objects C -> precategory_objects C' => 
    forall a b : precategory_objects C, a --> b -> x a --> x b) (pr1 F)
   (pr1 G)) (base_paths F G p).
*)
  simpl. 
(*  Print total2_paths2. *)
  apply (@total2_paths2 _ (fun p : pr1 (pr1 F) == pr1 (pr1 G) =>
          transportf
            (fun x : precategory_objects C -> precategory_objects C' =>
            (fun x0 : precategory_objects C -> precategory_objects C' => 
            forall a b : precategory_objects C, a --> b -> x0 a --> x0 b) x)
            p (pr2 (pr1 F)) == pr2 (pr1 G)) _ 
   (fiber_path_fibr (base_paths F G p)) _ (fiber_path_fibr (base_paths F G q))  H).
(*   Check fiber_path_fibr (base_paths F G q).
   Check (pr2 (pr1 G)).
*)
   apply uip.
(* Check impred.
*)
   change (isaset) with (isofhlevel 2).
   apply impred.
   intro a.
   apply impred.
   intro b.
   apply impred.
   intro f.
   apply (pr1 (pr1 G ) a --> pr1 (pr1 G) b).
(*   Check base_paths F G p.
   Check (fiber_path_fibr q).
   Check fiber_path_fibr p.
   Check @total2_paths2.
*)
   apply (@total2_paths2 (pr1 F == pr1 G)  
    (fun x : pr1 F == pr1 G => transportf _ x (pr2 F) == pr2 G)
(*
precategory_ob_mor_fun C C' =>
                   is_precategory_fun x) *)
          (base_paths F G p) (fiber_path_fibr p) (base_paths F G q) (fiber_path_fibr q) H').
(*   apply H3.
   Check fiber_path_fibr q.
*)
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

(** *** Fully faithful functors *)

Definition fully_faithful {C D : precategory} (F : precategory_fun C D) := 
  forall a b : precategory_objects C, 
    isweq (precategory_ob_mor_fun_morphisms F (a:=a) (b:=b)).

Definition fully_faithful_inv_hom (C D : precategory) (F : precategory_fun C D) 
      (HF : fully_faithful F) (a b : precategory_objects C)
      (f : F a --> F b) : a --> b :=
 invmap (tpair (fun f => isweq f) (precategory_ob_mor_fun_morphisms F (a:=a) (b:=b))
                            (HF a b)) f.


(** Fully faithful functors reflect isos *)

Lemma fully_faithful_reflects_iso (C D : precategory)(F : precategory_fun C D) 
        (HF : fully_faithful F)
    (a b : precategory_objects C) (f : iso_precat (F a) (F b)) : 
     is_precat_isomorphism (fully_faithful_inv_hom C D F HF a b f).
Proof.
  exists (fully_faithful_inv_hom C D F HF b a (inv_from_iso f)).
  simpl.
  unfold fully_faithful_inv_hom.
  split; simpl.
  unfold invmap. simpl.
  


(** ** Image on objects of a functor  *)
(** is used later to define the full image subcategory of a category [D] 
       defined by a functor [F : C -> D] *)

Definition is_in_img_precategory_fun {C D : precategory} (F : precategory_fun C D) 
      (d : precategory_objects D) :=
  ishinh (
  total2 (fun c : precategory_objects C => F c == d)).

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


(** * Sub-precategories *)

(** A sub-precategory is specified through a predicate on objects 
    and a dependent predicate on morphisms
    which is compatible with identity and composition
*)

Definition is_sub_precategory {C : precategory}
    (C' : hsubtypes (precategory_objects C))
    (Cmor' : forall a b:precategory_objects C, hsubtypes (a --> b)) :=
dirprod (forall a : precategory_objects C,
                         C' a ->  Cmor' _ _ (precategory_identity a ))
              (forall (a b c: precategory_objects C) (f: a --> b) (g : b --> c),
                   Cmor' _ _ f -> Cmor' _ _  g -> Cmor' _ _  (f ;; g)).

Definition sub_precategories (C : precategory) := total2 (
   fun C' : dirprod (hsubtypes (precategory_objects C))
                    (forall a b:precategory_objects C, hsubtypes (a --> b)) =>
        is_sub_precategory (pr1 C') (pr2 C')).

(** A full subcategory has the true predicate on morphisms *)

Lemma is_sub_precategory_full (C : precategory)
         (C':hsubtypes (precategory_objects C)) :
        is_sub_precategory C' (fun a b => fun f => htrue).
Proof.
  split; simpl;
  intros; exact tt.
Defined.
  
Definition full_sub_precategory {C : precategory}
         (C': hsubtypes (precategory_objects C)) :
   sub_precategories C :=
  tpair _  (dirprodpair C' (fun a b f => htrue)) (is_sub_precategory_full C C').


(** We have a coercion [carrier] turning every predicate [P] on a type [A] into the
     total space [ { a : A & P a} ].
   
   For later, we define some projections with the appropriate type, also to 
   avoid confusion with the aforementioned coercion.
*)

Definition sub_precategory_predicate_objects {C : precategory}
     (C': sub_precategories C):
       hsubtypes (precategory_objects C) := pr1 (pr1 C').

Definition sub_precategory_objects {C : precategory}(C': sub_precategories C): UU :=
     (*carrier*) (sub_precategory_predicate_objects C').


Definition sub_precategory_predicate_morphisms {C : precategory}
        (C':sub_precategories C)
      ( a b:precategory_objects C ) : hsubtypes (a --> b) := pr2 (pr1 C') a b.

Definition sub_precategory_morphisms {C : precategory}(C':sub_precategories C)
      (a b : precategory_objects C) : UU := 
         (*carrier*) (sub_precategory_predicate_morphisms C' a b).

(** Projections for compatibility of the predicate with identity and
    composition.
*)

Definition sub_precategory_id (C : precategory)(C':sub_precategories C) :
   forall a : precategory_objects C,
       sub_precategory_predicate_objects C' a -> 
       sub_precategory_predicate_morphisms  C' _ _ (precategory_identity a) :=
         pr1 (pr2 C').

Definition sub_precategory_comp (C : precategory)(C':sub_precategories C) :
   forall (a b c: precategory_objects C) (f: a --> b) (g : b --> c),
          sub_precategory_predicate_morphisms C' _ _ f -> 
          sub_precategory_predicate_morphisms C' _ _ g -> 
          sub_precategory_predicate_morphisms C' _ _  (f ;; g) :=
        pr2 (pr2 C').

(** the following lemma should be an instance of a general theorem saying that
     subtypes of a type of hlevel n are of hlevel n, but
     i haven't found that theorem
*)

Lemma is_set_sub_precategory_morphisms {C : precategory}(C':sub_precategories C)
      (a b : precategory_objects C) : isaset (sub_precategory_morphisms C' a b).
Proof.
  change (isaset) with (isofhlevel 2).
  apply isofhleveltotal2.
  apply (pr2 (a --> b)).
  intro f.
  apply isasetaprop.
  apply (pr2 (sub_precategory_predicate_morphisms C' a b f)).
Qed.

Definition sub_precategory_morphisms_set {C : precategory}(C':sub_precategories C)
      (a b : precategory_objects C) : hSet := 
    tpair _ (sub_precategory_morphisms C' a b)
        (is_set_sub_precategory_morphisms C' a b).


(** An object of a subcategory is an object of the original precategory. *)

Definition precategory_object_from_sub_precategory_object (C:precategory)
         (C':sub_precategories C) (a : sub_precategory_objects C') : 
    precategory_objects C := pr1 a.
Coercion precategory_object_from_sub_precategory_object : 
     sub_precategory_objects >-> precategory_objects.

(** A morphism of a subcategory is also a morphism of the original precategory. *)

Definition precategory_morphism_from_sub_precategory_morphism (C:precategory)
          (C':sub_precategories C) (a b : precategory_objects C)
           (f : sub_precategory_morphisms C' a b) : a --> b := pr1 f .
Coercion precategory_morphism_from_sub_precategory_morphism : 
         sub_precategory_morphisms >-> pr1hSet.


(** ** A sub-precategory forms a precategory. *)

Definition sub_precategory_ob_mor (C : precategory)(C':sub_precategories C) :
     precategory_ob_mor.
Proof.
  exists (sub_precategory_objects C').
  exact (fun a b => @sub_precategory_morphisms_set _ C' a b).
Defined.

(*
Coercion sub_precategory_ob_mor : sub_precategories >-> precategory_ob_mor.
*)


Definition sub_precategory_data (C : precategory)(C':sub_precategories C) :
      precategory_data.
Proof.
exists (sub_precategory_ob_mor C C').
split.
  intro c.
  exists (precategory_identity (C:=C) (pr1 c)).
  apply sub_precategory_id.
  apply (pr2 c).
  
  intros a b c f g.
  exists (precategory_compose (pr1 f) (pr1 g)).
  apply (sub_precategory_comp).
  apply f. apply g.
Defined.

(** A useful lemma for equality in the sub-precategory. *)

Lemma eq_in_sub_precategory (C : precategory)(C':sub_precategories C)
      (a b : sub_precategory_objects C') (f g : sub_precategory_morphisms C' a b) :
          pr1 f == pr1 g -> f == g.
Proof.
  intro H.
  destruct f as [f p].
  destruct g as [g p'].
  apply (total2_paths H).
  simpl. apply proofirrelevance. 
  apply (sub_precategory_predicate_morphisms C' a b g).
Qed.

(*
Lemma eq_in_sub_precategory2 (C : precategory)(C':sub_precategories C)
     (a b : sub_precategory_objects C') (f g : a --> b) 
 (pf : sub_precategory_predicate_morphisms C' _ _ f) 
 (pg : sub_precategory_predicate_morphisms C' _ _ g): 
  f == g -> (tpair (fun f => sub_precategory_predicate_morphisms _ _ _ f) f pf) == 
      (tpair (fun f => sub_precategory_predicate_morphisms _ _ _ f) g pg).
Proof.
  intro H.
  apply (total2_paths2 H).
  destruct H.
  apply (total2_paths2 (idpath _ )).
*)

Definition is_precategory_sub_category (C : precategory)(C':sub_precategories C) :
    is_precategory (sub_precategory_data C C').
Proof.
  repeat split;
  simpl; intros.
  unfold sub_precategory_comp.
  apply eq_in_sub_precategory. simpl.
  apply (precategory_id_left _ (pr1 a)).
  apply eq_in_sub_precategory. simpl.
  apply (precategory_id_right _ (pr1 a)).
  apply eq_in_sub_precategory.
  simpl.
  apply precategory_assoc.
Qed.

Definition carrier_of_sub_precategory (C : precategory)(C':sub_precategories C) :
   precategory := tpair _ _ (is_precategory_sub_category C C').

Coercion carrier_of_sub_precategory : sub_precategories >-> precategory.

(** An object satisfying the predicate is an object of the subcategory *)
Definition precategory_object_in_subcat {C : precategory} {C':sub_precategories C}
   (a : precategory_objects C)(p : sub_precategory_predicate_objects C' a) :
       precategory_objects C' := tpair _ a p.

(** A morphism satisfying the predicate is a morphism of the subcategory *)
Definition precategory_morphisms_in_subcat {C : precategory} {C':sub_precategories C}
   {a b : precategory_objects C'}(f : pr1 a --> pr1 b)
   (p : sub_precategory_predicate_morphisms C' (pr1 a) (pr1 b) (f)) :
       precategory_morphisms (C:=C') a b := tpair _ f p.

(** ** Functor from a sub-precategory to the ambient precategory *)

Definition sub_precategory_inclusion_data (C : precategory) (C':sub_precategories C):
  precategory_ob_mor_fun C' C. 
Proof.
  exists (@pr1 _ _ ). 
  intros a b. 
  exact (@pr1 _ _ ).
Defined.

Definition is_functor_sub_precategory_inclusion (C : precategory) 
         (C':sub_precategories C) :
    is_precategory_fun  (sub_precategory_inclusion_data C C').
Proof.
  split;
  simpl; 
  intros.
  apply (idpath _ ).
  apply (idpath _ ).
Qed.

 
Definition sub_precategory_inclusion (C : precategory)(C': sub_precategories C) :
    precategory_fun C' C := tpair _ _ (is_functor_sub_precategory_inclusion C C').

(** ** The (full) image of a functor *)

Definition full_img_sub_precategory {C D : precategory}(F : precategory_fun C D) :
    sub_precategories D := 
       full_sub_precategory (sub_img_precategory_fun F).

(** ** Given a functor F : C -> D, we obtain a functor F : C -> Img(F) *)

Definition full_img_functor_obj {C D : precategory}(F : precategory_fun C D) :
   precategory_objects C -> precategory_objects (full_img_sub_precategory F).
Proof.
  intro c.
  simpl.
  exists (F c).
  simpl.
  intros a b.
  apply b.
  exists c.
  apply idpath.
Defined.

Definition full_img_functor_data {C D : precategory}(F : precategory_fun C D) :
  precategory_ob_mor_fun C (full_img_sub_precategory F).
Proof.
  exists (full_img_functor_obj F).
  simpl.
  intros a b f.
  exists (#F f).
  exact tt.
Defined.

Lemma is_precategory_fun_full_img (C D: precategory) (F : precategory_fun C D) :
  is_precategory_fun (full_img_functor_data F).
Proof.
  split; simpl. 
  intro a. 
   assert (H : pr1 (tpair (fun f => htrue) (#F (precategory_identity a)) tt ) ==
               pr1 (precategory_identity (full_img_functor_obj F a))).
   simpl. apply precategory_fun_id.
  apply (total2_paths H).
  apply proofirrelevance.
  apply htrue.
  
  intros a b c f g.
  set ( H := eq_in_sub_precategory D (full_img_sub_precategory F)).
  set (H':= H (full_img_functor_obj F a)(full_img_functor_obj F c)).
  apply H'.
  simpl.
  apply precategory_fun_comp.
Qed.

Definition precategory_fun_full_img {C D: precategory} 
       (F : precategory_fun C D) :
   precategory_fun C (full_img_sub_precategory F) :=
   tpair _ _ (is_precategory_fun_full_img C D F).


(** *** Small exercise: Morphisms in the full subcategory are equivalent to 
        morphisms in the precategory *)
(** does of course not need the saturation hypothesis *)

Definition hom_in_subcat_from_hom_in_precat (C : precategory) 
 (C' : hsubtypes (precategory_objects C))
  (a b : precategory_objects (full_sub_precategory C'))
      (f : pr1 a --> pr1 b) : a --> b := 
       tpair _ f tt.

Definition hom_in_precat_from_hom_in_full_subcat (C : precategory) 
 (C' : hsubtypes (precategory_objects C))
  (a b : precategory_objects (full_sub_precategory C')) :
     a --> b -> pr1 a --> pr1 b := @pr1 _ _ .


Lemma isweq_hom_in_precat_from_hom_in_full_subcat (C : precategory) 
 (C' : hsubtypes (precategory_objects C))
    (a b : precategory_objects (full_sub_precategory C')): 
 isweq (hom_in_precat_from_hom_in_full_subcat _ _ a b).
Proof.
  apply (gradth _ 
         (hom_in_subcat_from_hom_in_precat _ _ a b)).
  intro f. 
  destruct f. simpl.
  apply eq_in_sub_precategory.
  simpl.
  apply idpath.
  intros. apply idpath.
Qed.

Lemma isweq_hom_in_subcat_from_hom_in_precat (C : precategory) 
 (C' : hsubtypes (precategory_objects C))
    (a b : precategory_objects (full_sub_precategory C')): 
 isweq (hom_in_subcat_from_hom_in_precat  _ _ a b).
Proof.
  apply (gradth _ 
         (hom_in_precat_from_hom_in_full_subcat _ _ a b)).
  intro f. 
  intros. apply idpath.
  intro f.
  destruct f. simpl.
  apply eq_in_sub_precategory.
  simpl.
  apply idpath.
Qed.

Definition weq_hom_in_subcat_from_hom_in_precat (C : precategory) (C' : hsubtypes (precategory_objects C))
    (a b : precategory_objects (full_sub_precategory C')): weq (pr1 a --> pr1 b) (a-->b) :=
  tpair _ _ (isweq_hom_in_subcat_from_hom_in_precat C C' a b).


Lemma trivial (C D : precategory) (F : precategory_fun C D) (a : precategory_objects C):
    is_in_img_precategory_fun F (F a).
Proof.
  apply hinhpr.
  exists a.
  exact (idpath _).
Defined.



Lemma precategory_fun_full_img_fully_faithful_if_fun_is (C D : precategory)
   (F : precategory_fun C D) (H : fully_faithful F) : 
   fully_faithful (precategory_fun_full_img F).
Proof.
  unfold fully_faithful in *.
  intros a b.
  set (H' := weq_hom_in_subcat_from_hom_in_precat).
  set (H'' := H' D (is_in_img_precategory_fun F)).
(*  assert (Hx : (precategory_objects (full_sub_precategory (is_in_img_precategory_fun F)))).
      exists (F a).
        simpl. apply hinhpr. exists a. apply idpath. *)
  set (Fa := tpair (fun a : precategory_objects D => is_in_img_precategory_fun F a) 
        (F a) (trivial _ _ F a)).
  set (Fb := tpair (fun a : precategory_objects D => is_in_img_precategory_fun F a) 
        (F b) (trivial _ _ F b)).
  set (H3 := (H'' Fa Fb)).
  assert (H2 : precategory_ob_mor_fun_morphisms (precategory_fun_full_img F) (a:=a) (b:=b) == 
                  funcomp (precategory_ob_mor_fun_morphisms F (a:=a) (b:=b))
                          ((H3))).
  apply funextsec. intro f.
  simpl.
  unfold funcomp.
  unfold hom_in_subcat_from_hom_in_precat. simpl.
  unfold invmap.
  apply idpath.

  rewrite H2.
  apply twooutof3c.
  apply H.
  apply (H3).
Qed.
  
 


(** *** Image factorization C -> Img(F) -> D *)

Lemma precategory_fun_full_img_factorization_ob (C D: precategory) 
   (F : precategory_fun C D):
  precategory_ob_mor_fun_objects F == 
  precategory_ob_mor_fun_objects (precategory_fun_composite _ _ _ 
       (precategory_fun_full_img F) 
            (sub_precategory_inclusion D _)).
Proof.
  simpl.
  apply etacorrection.
Defined.


(**  works up to eta conversion *)

(*
Lemma precategory_fun_full_img_factorization (C D: precategory) 
                (F : precategory_fun C D) :
    F == precategory_fun_composite _ _ _ (precategory_fun_full_img F) 
            (sub_precategory_inclusion D _).
Proof.
  apply precategory_fun_eq. About precategory_fun_full_img_factorization_ob.
  set (H := precategory_fun_full_img_factorization_ob C D F).
  simpl in *.
  destruct F as [F Fax].
  simpl. 
  destruct F as [Fob Fmor]; simpl in *.
  apply (total2_paths2 (H)).
  unfold precategory_fun_full_img_factorization_ob in H.
  simpl in *.
  apply dep_funextfunax.
  intro a.
  apply dep_funextfunax.
  intro b.
  apply funextfunax.
  intro f.
  
  generalize Fmor.
  clear Fax.
  assert (H' : Fob == (fun a : precategory_objects C => Fob a)).
   apply H.

  generalize dependent a .
  generalize dependent b.
  clear Fmor. 
    generalize H.
  clear H.
  intro H.
  clear H'.
  destruct H.
  tion H.
  induction  H'.
  induction H'.
  clear H.
  
*)


(** ** Any full subcategory of a saturated category is saturated. *)


Section full_sub_sat.

Variable C : precategory.
Hypothesis H : is_saturated C.

Variable C' : hsubtypes (precategory_objects C).
(*

Variables a b : precategory_objects (full_sub_precategory C').

Variable f : iso_precat a b.

*)
(*
Definition arrow_in_precat : precategory_morphisms (C:=C) (pr1 a) (pr1 b) :=
      pr1 (pr1 f).
  apply f.
Defined.
Print arrow_in_precat.
 := pr1 f.
*)






(** *** Isos in the full subcategory are equivalent to isos in the precategory *)

Lemma iso_in_subcat_is_iso_in_precat (a b : precategory_objects (full_sub_precategory C'))
       (f : iso_precat a b): is_precat_isomorphism (C:=C) (a:=pr1 a) (b:=pr1 b) 
     (pr1 (pr1 f)).
Proof.
  destruct f as [f fp].
  destruct fp as [g gx]. simpl in *.
  exists g.
(*  destruct f as [f pp]. *)
  destruct gx; simpl in *.
  split; simpl.
  apply (base_paths _ _ pr1).
  apply (base_paths _ _ pr2).
Qed.

Lemma iso_in_precat_is_iso_in_subcat (a b : precategory_objects (full_sub_precategory C'))
     (f : iso_precat (pr1 a) (pr1 b)) : 
   is_precat_isomorphism (C:=full_sub_precategory C')  
     (precategory_morphisms_in_subcat f tt).
Proof.
  destruct f as [f fp].
  destruct fp as [g gax].
  destruct gax as [g1 g2].
  exists (precategory_morphisms_in_subcat g tt).
  split; simpl in *.
  apply eq_in_sub_precategory. simpl.
  assumption.
  apply eq_in_sub_precategory. simpl.
  assumption.
Qed.

Definition iso_from_iso_in_sub (a b : precategory_objects (full_sub_precategory C'))
       (f : iso_precat a b) : iso_precat (pr1 a) (pr1 b) :=
   tpair _ _ (iso_in_subcat_is_iso_in_precat a b f).

Definition iso_in_sub_from_iso (a b : precategory_objects (full_sub_precategory C'))
   (f : iso_precat (pr1 a) (pr1 b)) : iso_precat a b :=
    tpair _ _ (iso_in_precat_is_iso_in_subcat a b f).

Lemma isweq_iso_from_iso_in_sub (a b : precategory_objects (full_sub_precategory C')):
     isweq (iso_from_iso_in_sub a b).
Proof.
  apply (gradth _ (iso_in_sub_from_iso a b)).
  intro f.
  apply eq_iso_precat.
  simpl.
  apply eq_in_sub_precategory.
  simpl.
  apply idpath.
  intro f.
  apply eq_iso_precat.
  simpl.
  apply idpath.
Qed.

Lemma isweq_iso_in_sub_from_iso (a b : precategory_objects (full_sub_precategory C')):
     isweq (iso_in_sub_from_iso a b).
Proof.
  apply (gradth _ (iso_from_iso_in_sub a b)).
  intro f.
  apply eq_iso_precat.
  simpl.
  apply idpath.
  simpl.
  intro f.
  apply eq_iso_precat.
  simpl.
  apply eq_in_sub_precategory.
  apply idpath.
Qed.


(** *** From Identity in the subcategory to isos in the category  *)
(** This gives a weak equivalence *)
Definition Id_in_sub_to_iso (a b : precategory_objects (full_sub_precategory C')):
     a == b -> iso_precat (pr1 a) (pr1 b) :=
       funcomp (precat_paths_to_iso a b) (iso_from_iso_in_sub a b).

Lemma Id_in_sub_to_iso_equal_iso_precat 
  (a b : precategory_objects (full_sub_precategory C')) :
    Id_in_sub_to_iso a b == 
funcomp (total_paths2_hProp_equiv C' a b)
        (precat_paths_to_iso (C:=C) (pr1 a) (pr1 b)).
Proof.
  apply funextfunax.
  intro p.
  destruct p.
  apply eq_iso_precat;
  simpl; apply idpath.
Qed.

Lemma isweq_Id_in_sub_to_iso (a b : precategory_objects (full_sub_precategory C')):
    isweq (Id_in_sub_to_iso a b).
Proof.
  rewrite Id_in_sub_to_iso_equal_iso_precat.
  apply twooutof3c.
  apply (total_paths2_hProp_equiv C' a b).
  apply H.
Qed.
Check Id_in_sub_to_iso.
(** *** Decomposition of the map from identities in the subcat to 
       isos in the subcat via isos in the category  *)

Lemma precat_paths_in_sub_as_3_maps
   (a b : precategory_objects (full_sub_precategory C')):
     precat_paths_to_iso a b == funcomp (Id_in_sub_to_iso a b) 
                                        (iso_in_sub_from_iso a b).
Proof.
  apply funextfunax.
  intro p.
  destruct p.
  simpl.
  apply eq_iso_precat.
  simpl.
  unfold precategory_morphisms_in_subcat.
  apply eq_in_sub_precategory.
  simpl.
  apply idpath.
Qed.

(** *** The aforementioned decomposed map is a weak equivalence since
        its decomposition pieces are *)

Lemma isweq_sub_precat_paths_to_iso 
  (a b : precategory_objects (full_sub_precategory C')) :
 isweq (precat_paths_to_iso a b).
Proof.
  rewrite precat_paths_in_sub_as_3_maps.
  apply twooutof3c.
  apply isweq_Id_in_sub_to_iso.
  apply isweq_iso_in_sub_from_iso.
Qed.

(** ** Proof of the targeted theorem: full subcats of cats are cats *)

Lemma is_saturated_full_subcat: is_saturated (full_sub_precategory C').
Proof.
  unfold is_saturated.
  apply isweq_sub_precat_paths_to_iso.
Qed.




End full_sub_sat.
    
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
  (F F' : precategory_ob_mor_fun C C') (t : forall x : precategory_objects C, F x -->  F' x) :
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
(*  Search ( isaset). *)
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
Print precategory_ob_mor_fun.
Print is_precategory_fun_fun.
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
Check @toforallpaths.

(*
Definition pr1_pr1_functor_eq_from_functor_iso_on_idtoiso (C D : precategory)
    (H : is_saturated D) (F G : precategory_objects [C , D]) 
    (p : F == G) : forall a : precategory_objects C,
    toforallpaths _ _ _ (pr1_pr1_functor_eq_from_functor_iso _ _ _ _ _ (idtoiso p)) a  ==
         idtoiso _ (maponpaths (@pr1 _ _ ) (maponpaths (@pr1 _ _ ) p)) a.
   iso_precat F G -> pr1 (pr1 F) == pr1 (pr1 G).
*)


Lemma weird_lemma (C D : precategory) 
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
  rewrite weird_lemma.
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
(*  set (H3 := precategory_fun_fun_ax _ _ (A) a b f).
  simpl in *. *)
  pathvia 
    (inv_from_iso (precategory_fun_iso_pointwise_if_iso C D F G A Aiso a) ;;
       (A a ;; #G f)).
  rewrite <- precategory_assoc.
  apply maponpaths.
  apply (precategory_fun_fun_ax _ _ A).
  rewrite precategory_assoc.
(*  set (H5 := is_precategory_fun_iso_pointwise_if_iso _ _ _ _ A Aiso a).*)
  unfold precategory_fun_iso_pointwise_if_iso.
  unfold inv_from_iso.
  simpl in *.
(*  destruct H5 as [x y].
  simpl in *.
  destruct y as [y1 y2].*)
(*  unfold is_precategory_fun_iso_pointwise_if_iso. *)
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


Lemma idtoiso_compute_pointwise (C D : precategory)
  (*H : is_saturated D*) (F G : precategory_objects [C, D])
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
  
(* here maybe use transport of equality along weq toforallpath *)  
  Check equal_transport_along_weq.
  apply (equal_transport_along_weq _ _  _ _ (weqtoforallpaths _ _ _ )).
  
  simpl.
  rewrite toforallpaths_funextsec.
  simpl.
  apply funextsec.
  intro a. Check (pr2 (idtoiso p)).
  rewrite idtoiso_compute_pointwise.
  
(*  
  pathvia (isotoid D H
       
    (idtoiso (     toforallpaths (fun _ : precategory_objects C => D) (pr1 (pr1 F)) (pr1 (pr1 G))
  (base_paths (pr1 F) (pr1 G) (base_paths F G p)) a))

).
  apply maponpaths.
  induction p.
  simpl.
  Check identity_iso_precat (pr1 (pr1 F) a).
  apply eq_iso_precat. simpl. apply idpath.
*)
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
  Check idtoiso_compute_pointwise.
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
Check isotoid.

  pathvia (pr1 (idtoiso
     (
        (* toforallpaths (fun _ : C => D) (pr1 (pr1 F)) (pr1 (pr1 G))
            (pr1_pr1_functor_eq_from_functor_iso C D H F G gamma) a *)
         isotoid D H (precategory_fun_iso_pointwise_if_iso C D F G gamma (pr2 gamma) a)
      ))).
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


