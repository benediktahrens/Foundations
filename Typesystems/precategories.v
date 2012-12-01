Add Rec LoadPath "../Generalities".
Add Rec LoadPath "../hlevel1".
Add Rec LoadPath "../hlevel2".

Require Import uu0.
Require Import hSet.

Notation "a == b" := (paths a b) (at level 70, no associativity).
Notation "! p " := (pathsinv0 p) (at level 50).
Notation "p @ q" := (pathscomp0 p q) (at level 60, right associativity).


(** * Definition of a precategory *)
(** ** Space of types (objects) together with a fibration (morphisms) *)

Definition precategory_ob_mor := total2 (
  fun ob : UU => ob -> ob -> hSet).

Definition precategory_objects (C : precategory_ob_mor) : UU :=
    pr1 C.
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

Definition precategory := total2 (
  fun C : precategory_data => 
    dirprod (dirprod (forall (a b : precategory_objects C) (f : a --> b),
                         precategory_identity a ;; f == f)
                     (forall (a b : precategory_objects C) (f : a --> b),
                         f ;; precategory_identity b == f))
            (forall (a b c d : precategory_objects C) 
                    (f : a --> b)(g : b --> c) (h : c --> d),
                     f ;; (g ;; h) == (f ;; g) ;; h)).

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

Coercion sub_precategory_ob_mor : sub_precategories >-> precategory_ob_mor.


Definition sub_precategory_data (C : precategory)(C':sub_precategories C) :
      precategory_data.
exists (sub_precategory_ob_mor C C').
split.
  intro c.
  simpl. unfold sub_precategory_morphisms. simpl.
  unfold sub_precategory_predicate_morphisms. simpl.
  exists (precategory_identity (C:=C)).
 intros.


Definition sub_precategory_id_closed (C : precategory)(C':sub_precategories C) :
    forall a : precategory_objects C,
       sub_precategory_predicate_objects C' a -> 
    sub_precategory_morphisms C' (precategory_identity a ).

Definition sub_precategory_comp_closed (C : precategory)(C':sub_precategories C) :
   forall (a b c: precategory_objects C) (f: a --> b) (g : b --> c),
              sub_precategory_morphisms C' f -> 
              sub_precategory_morphisms C' g -> 
              sub_precategory_morphisms C' (f ;; g).

Definition sub_precategory_ob_mor (C : precategory)(C':sub_precategories C) :
     precategory_ob_mor.
  exists (sub_precategory_objects C').
  exact (fun a b => @sub_precategory_morphisms _ C' a b).
  exact (

Definition is_precategory_sub_precategory (C : precategory)(C':sub_precategories C) :
   precategory.


(** * Natural transformations *)






