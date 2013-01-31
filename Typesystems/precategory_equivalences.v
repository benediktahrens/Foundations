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




Check triangle_id_right_ad.









(*
Definition left_adjoint (C D : precategory) (F : precategory_object [C,D]) :=
   total2
*)