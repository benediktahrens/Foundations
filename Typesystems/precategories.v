Add Rec LoadPath "../Generalities".
Add Rec LoadPath "../hlevel1".
Add Rec LoadPath "../hlevel2".

Require Import basic_lemmas_which_should_be_in_uu0.
Require Import uu0.
Require Import hSet.

Notation "a == b" := (paths a b) (at level 70, no associativity).
Notation "! p " := (pathsinv0 p) (at level 50).
Notation "p @ q" := (pathscomp0 p q) (at level 60, right associativity).


(** * Definition of a precategory *)
(** ** Space of types (objects) together with a fibration (morphisms) *)

Definition precategory_ob_mor := total2 (
  fun ob : UU => ob -> ob -> hSet).

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

Definition precategory_ob_mor_from_precategory_data (C : precategory_data) :
     precategory_ob_mor := pr1 C.
Coercion precategory_ob_mor_from_precategory_data : 
  precategory_data >-> precategory_ob_mor.

Definition precategory_identity { C : precategory_data } :
    forall c : precategory_objects C, c --> c := 
         pr1 (pr2 C).

Definition precategory_compose { C : precategory_data } 
  { a b c : precategory_objects C } : 
                 a --> b ->
                 b --> c ->
                 a --> c :=
   pr2 (pr2 C) a b c.

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
(*  fun C : precategory_data => 
    dirprod (dirprod (forall (a b : precategory_objects C) (f : a --> b),
                         precategory_identity a ;; f == f)
                     (forall (a b : precategory_objects C) (f : a --> b),
                         f ;; precategory_identity b == f))
            (forall (a b c d : precategory_objects C) 
                    (f : a --> b)(g : b --> c) (h : c --> d),
                     f ;; (g ;; h) == (f ;; g) ;; h)).
*)

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

Definition precategory_eq_morphism (C : precategory_data) (a b : precategory_objects C)
      (H : a == b) : a --> b.
Proof.
  destruct H.
  exact (precategory_identity a).
Defined.

Definition precategory_eq_morphism_inv (C : precategory_data) (a b : precategory_objects C)
      (H : a == b) : b --> a.
Proof.
  destruct H.
  exact (precategory_identity a).
Defined.

(** ** Setcategories: Precategories whose objects form a set *)

Definition setcategory := total2 (
   fun C : precategory => isaset (precategory_objects C)).

Definition precategory_from_setcategory (C : setcategory) : precategory := pr1 C.
Coercion precategory_from_setcategory : setcategory >-> precategory.

(** TODO : this is injective *)


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

Definition precategory_fun (C C' : precategory_data) := total2 (
   fun F : precategory_ob_mor_fun C C' => 
     dirprod (forall a : precategory_objects C, 
                 #F (precategory_identity a) == precategory_identity (F a))
             (forall a b c : precategory_objects C, forall f : a --> b,
                 forall g : b --> c, 
                #F (f ;; g) == #F f ;; #F g)).

Definition precategory_ob_mor_fun_from_precategory_fun (C C': precategory_data)
     (F : precategory_fun C C') : precategory_ob_mor_fun C C' := pr1 F.
Coercion precategory_ob_mor_fun_from_precategory_fun : precategory_fun >->
      precategory_ob_mor_fun.


Definition precategory_fun_id (C C' : precategory_data)(F : precategory_fun C C') :
       forall a : precategory_objects C, 
                 #F (precategory_identity a) == precategory_identity (F a) :=
     pr1 (pr2 F).

Definition precategory_fun_comp (C C' : precategory_data)(F : precategory_fun C C') :
       forall a b c : precategory_objects C, forall f : a --> b,
                 forall g : b --> c, 
                #F (f ;; g) == #F f ;; #F g := pr2 (pr2 F).


(** ** Composition of Functors, Identity Functors *)

(** to do *)

(** * Sub-precategories *)


Definition sub_precategories (C : precategory) := total2 (
   fun C' : dirprod (hsubtypes (precategory_objects C))
                    (forall a b:precategory_objects C, hsubtypes (a --> b)) =>
      dirprod (forall a : precategory_objects C,
                         pr1 C' a -> pr2 C' _ _ (precategory_identity a ))
              (forall (a b c: precategory_objects C) (f: a --> b) (g : b --> c),
                   pr2 C' _ _ f -> pr2 C' _ _  g -> pr2 C' _ _  (f ;; g))).


(** we have a coercion [carrier] turning every predicate [P] on a type [A] into the
     total space [ { a : A & P a} ].
*)

Definition sub_precategory_predicate_objects {C : precategory}(C': sub_precategories C) :
       hsubtypes (precategory_objects C) := pr1 (pr1 C').

Definition sub_precategory_objects {C : precategory}(C': sub_precategories C) : UU :=
     (*carrier*) (sub_precategory_predicate_objects C').


Definition sub_precategory_predicate_morphisms {C : precategory}(C':sub_precategories C)
      ( a b:precategory_objects C ) : hsubtypes (a --> b) := pr2 (pr1 C') a b.

Definition sub_precategory_morphisms {C : precategory}(C':sub_precategories C)
      (a b : precategory_objects C) : UU := 
         (*carrier*) (sub_precategory_predicate_morphisms C' a b).


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
    tpair _ (sub_precategory_morphisms C' a b)(is_set_sub_precategory_morphisms C' a b).

Definition precategory_object_from_sub_precategory_object (C:precategory)
         (C':sub_precategories C) (a : sub_precategory_objects C') : 
    precategory_objects C := pr1 a.
Coercion precategory_object_from_sub_precategory_object : 
     sub_precategory_objects >-> precategory_objects.

Definition precategory_morphism_from_sub_precategory_morphism (C:precategory)
          (C':sub_precategories C) (a b : precategory_objects C)
           (f : sub_precategory_morphisms C' a b) : a --> b := pr1 f .
Coercion precategory_morphism_from_sub_precategory_morphism : 
         sub_precategory_morphisms >-> pr1hSet.


Definition sub_precategory_ob_mor (C : precategory)(C':sub_precategories C) :
     precategory_ob_mor.
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


Lemma eq_in_sub_precategory (C : precategory)(C':sub_precategories C)
      (a b : sub_precategory_objects C') (f g : sub_precategory_morphisms C' a b) :
          pr1 f == pr1 g -> f == g.
Proof.
  intro H.
  destruct f as [f p].
  destruct g as [g p']. Search total2.
  apply (total2_paths H).
  simpl. apply proofirrelevance. 
  apply (sub_precategory_predicate_morphisms C' a b g).
Qed.


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


    
(** ** Precategories in style of essentially algebraic cats *)
(** Of course we later want SETS of objects, rather than types,
    but the construction can already be specified.
*)
       
Definition precategory_total_morphisms (C : precategory_ob_mor) := total2 (
   fun ab : dirprod (precategory_objects C)(precategory_objects C) =>
        precategory_morphisms (pr1 ab) (pr2 ab)).

Lemma isaset_setcategory_total_morphisms (C : setcategory) : 
   isaset (precategory_total_morphisms C).

Definition precategory_source (C : precategory_ob_mor) : 
     precategory_total_morphisms C -> precategory_objects C := 
     fun abf => pr1 (pr1 abf).

Definition precategory_target (C : precategory_ob_mor) : 
     precategory_total_morphisms C -> precategory_objects C := 
     fun abf => pr2 (pr1 abf).

Definition precategory_total_id (C : precategory_data) : 
      precategory_objects C -> precategory_total_morphisms C :=
      fun c => tpair _ (dirprodpair c c) (precategory_identity c).

Definition precategory_total_comp (C : precategory_data) : 
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








