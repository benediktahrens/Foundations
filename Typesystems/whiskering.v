(** **********************************************************

Benedikt Ahrens and Chris Kapulkin
january 2013


************************************************************)


(** **********************************************************

Contents : 

- Precomposition with a functor for 
   - functors and
   - natural transformations (whiskering)

- Functoriality of precomposition	

- Precomposition with an essentially surjective 
	   functor yields a faithful functor

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
Require Import functors_transformations.

Notation "a == b" := (paths a b) (at level 70, no associativity).
Notation "! p " := (pathsinv0 p) (at level 50).
Notation "p @ q" := (pathscomp0 p q) (at level 60, right associativity).

Ltac pathvia b := (apply (@pathscomp0 _ _ b _ )).

Local Notation "a --> b" := (precategory_morphisms a b)(at level 50).
(*Local Notation "'hom' C" := (precategory_morphisms (C := C)) (at level 2).*)
Local Notation "f ;; g" := (precategory_compose f g)(at level 50).
Notation "[ C , D ]" := (precategory_fun_precategory C D).
Local Notation "# F" := (precategory_ob_mor_fun_morphisms F)(at level 3).


Definition functor_composite (A B C : precategory) (F : ob [A, B])
      (G : ob [B , C]) : ob [A , C] := 
   precategory_fun_composite _ _ _ F G.

Notation "G 'O' F" := (functor_composite _ _ _ F G) (at level 25).

(** * Whiskering: Composition of a natural transformation with a functor *)

(** Prewhiskering *)

Lemma is_precat_fun_fun_pre_whisker (A B C : precategory) (F : ob [A, B])
   (G H : ob [B, C]) (gamma : G --> H) : 
  is_precategory_fun_fun (precategory_fun_composite _ _ _ F G ) 
                         (precategory_fun_composite _ _ _ F H) 
     (fun a : ob A => pr1 gamma ((pr1 F) a)).
Proof.
  unfold is_precategory_fun_fun.
  simpl.
  intros x x' f.
  rewrite  (precategory_fun_fun_ax _ _ gamma).
  apply idpath.
Qed.

Definition pre_whisker (A B C : precategory) (F : ob [A, B])
   (G H : ob [B, C]) (gamma : G --> H) : 
       G O F --> H O F.
Proof.
  exists (fun a => pr1 gamma (pr1 F a)).
  apply is_precat_fun_fun_pre_whisker.
Defined.

(** Postwhiskering *)

Lemma is_precat_fun_fun_post_whisker (B C D : precategory) 
   (G H : ob [B, C]) (gamma : G --> H) 
        (K : ob [C, D]): 
  is_precategory_fun_fun (precategory_fun_composite _ _ _ G K) 
                         (precategory_fun_composite _ _ _ H K) 
     (fun a : ob B => # (pr1 K) (pr1 gamma  a)).
Proof.
  unfold is_precategory_fun_fun.
  simpl in *.
  intros x x' f.
  repeat rewrite <- precategory_fun_comp.
  rewrite  (precategory_fun_fun_ax _ _ gamma).
  apply idpath.
Qed.

Definition post_whisker (B C D : precategory) 
   (G H : ob [B, C]) (gamma : G --> H) 
        (K : ob [C, D]) : K O G --> K O H.
Proof.
  exists (fun a : ob B => # (pr1 K) (pr1 gamma  a)).
  apply is_precat_fun_fun_post_whisker.
Defined.

(** Precomposition with a functor is functorial *)
(** Postcomposition is, too, but that's not of our concern for now. *)

Definition pre_composition_precategory_ob_mor_fun (A B C : precategory)
      (H : ob [A, B]) : precategory_ob_mor_fun [B,C] [A,C].
Proof.
  exists (fun G => G O H).
  exact (fun a b gamma => pre_whisker _ _ _ H _ _ gamma).
Defined.

Lemma pre_composition_is_precategory_fun (A B C : precategory) (H : ob [A, B]) :
    is_precategory_fun (pre_composition_precategory_ob_mor_fun A B C H).
Proof.
  split; simpl.
  intro G.
  apply precategory_fun_fun_eq.
  intro a. apply idpath.
  
  intros K L M a b.
  apply precategory_fun_fun_eq.
  unfold pre_whisker.
  intro x.
  apply idpath.
Qed.

Definition pre_composition_functor (A B C : precategory) (H : ob [A , B]) :
      precategory_fun [B, C] [A, C].
Proof.
  exists (pre_composition_precategory_ob_mor_fun A B C H).
  apply pre_composition_is_precategory_fun.
Defined.



  






