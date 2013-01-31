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

Lemma is_precat_fun_fun_left_whisker (A B C : precategory) (F : precategory_objects [A, B])
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

Definition left_whisker (A B C : precategory) (F : precategory_objects [A, B])
   (G H : precategory_objects [B, C]) (gamma : G --> H) : 
       G O F --> H O F.
Proof.
  exists (fun a => pr1 gamma (pr1 F a)).
  apply is_precat_fun_fun_left_whisker.
Defined.




Lemma is_precat_fun_fun_right_whisker (B C D : precategory) 
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

Definition right_whisker (B C D : precategory) 
   (G H : precategory_objects [B, C]) (gamma : G --> H) 
        (K : precategory_objects [C, D]) : K O G --> K O H.
Proof.
  exists (fun a : precategory_objects B => # (pr1 K) (pr1 gamma  a)).
  apply is_precat_fun_fun_right_whisker.
Defined.













(*
Definition left_adjoint (C D : precategory) (F : precategory_object [C,D]) :=
   total2
*)