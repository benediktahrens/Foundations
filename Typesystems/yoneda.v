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
Require Import precategory_of_hsets.

Notation "a == b" := (paths a b) (at level 70, no associativity).
Notation "! p " := (pathsinv0 p) (at level 50).
Notation "p @ q" := (pathscomp0 p q) (at level 60, right associativity).

Local Notation "a --> b" := (precategory_morphisms a b)(at level 50).
Local Notation "f ;; g" := (precategory_compose f g)(at level 50).

Ltac pathvia b := (apply (@pathscomp0 _ _ b _ )).


(** * The opposite precategory of a precategory *)

Definition opp_precat_op_mor (C : precategory_ob_mor) : precategory_ob_mor :=
   tpair (fun ob : UU => ob -> ob -> hSet) (precategory_objects C) 
        (fun a b : precategory_objects C => b --> a).

Definition opp_precat_data (C : precategory_data) : precategory_data.
Proof.
  exists (opp_precat_op_mor C).
  split.
  exact (fun c => precategory_identity c).
  simpl.
  intros a b c f g.
  exact (g ;; f).
Defined.

Hint Unfold precategory_identity.

Ltac unf := unfold precategory_identity, 
                   precategory_compose, 
                   precategory_morphisms;
                   simpl.

Lemma is_precat_opp_precat_data (C : precategory) : is_precategory (opp_precat_data C).
Proof.
  repeat split; simpl.
  intros. unf.
  apply precategory_id_right.
  intros; unf.
  apply precategory_id_left.
  intros; unf.
  rewrite precategory_assoc.
  apply idpath.
Qed.

Definition opp_precat (C : precategory) : precategory := 
  tpair _ (opp_precat_data C) (is_precat_opp_precat_data C).

Notation "C '^op'" := (opp_precat C) (at level 3).


Definition yoneda_objects_ob (C : precategory) (c : precategory_objects C)
          (d : precategory_objects C) := d --> c.

Definition yoneda_objects_mor (C : precategory) (c : precategory_objects C)
    (d d' : precategory_objects C) (f : d --> d') :
   yoneda_objects_ob C c d' -> yoneda_objects_ob C c d :=
    fun g => f ;; g.

Definition yoneda_precategory_morphisms_ob_mor_fun 
 (C : precategory) (c : precategory_objects C) :
    precategory_ob_mor_fun (C^op) HSET.
Proof.
  exists (yoneda_objects_ob C c).
  simpl.
  unf. unfold yoneda_objects_ob. unf. simpl.
  intros a b f g.
  exact (f ;; g).
Defined.


Lemma is_functor_yoneda_precategory_ob_mor_fun (C : precategory) (c : precategory_objects C) :
  is_precategory_fun (yoneda_precategory_morphisms_ob_mor_fun C c).
Proof.
  repeat split; unf; simpl.
  intros.
  apply funextsec.
  intro f. unf. apply precategory_id_left.
  intros a b d f g.
  apply funextsec. intro h.
  apply (! precategory_assoc _ _ _ _ _ _ _ _ ).
Qed.

Definition yoneda_objects (C : precategory) (c : precategory_objects C) : 
(*           precategory_objects [C^op, HSET] := *)
             precategory_fun C^op HSET :=
    tpair _ _ (is_functor_yoneda_precategory_ob_mor_fun C c).

Definition yoneda_morphisms_data (C : precategory)(c c' : precategory_objects C) 
    (f : c --> c') : forall a : precategory_objects C^op, 
           yoneda_objects C c a --> yoneda_objects C c' a := 
            fun a g => g ;; f.

Lemma is_precategory_fun_fun_yoneda_morphisms_data (C : precategory) 
     (c c' : precategory_objects C) (f : c --> c') :
  is_precategory_fun_fun  
         (yoneda_objects C c) 
         (yoneda_objects C c') 
    (yoneda_morphisms_data C c c' f).
Proof.
  unfold is_precategory_fun_fun.
  simpl. unfold yoneda_morphisms_data.
  simpl.
  intros d d' g.
  apply funextsec; simpl in *.
  unfold yoneda_objects_ob. simpl.
  unf.
  intro h.
  apply  ( ! precategory_assoc _ _ _ _ _ _ _ _  ).
Qed.

Definition yoneda_morphisms (C : precategory) (c c' : precategory_objects C)
   (f : c --> c') : precategory_fun_fun (yoneda_objects C c) (yoneda_objects C c') :=
   tpair _ _ (is_precategory_fun_fun_yoneda_morphisms_data C c c' f).


Definition yoneda_precategory_ob_mor_fun (C : precategory): 
   precategory_ob_mor_fun C [C^op , HSET] := 
   tpair _ (yoneda_objects C) (yoneda_morphisms C).


Lemma is_precategory_fun_yoneda (C : precategory) :
  is_precategory_fun (yoneda_precategory_ob_mor_fun C).
Proof.
  unfold is_precategory_fun.
  repeat split; simpl.
  intro a.
  apply precategory_fun_fun_eq.
  simpl.
  unfold yoneda_morphisms_data, yoneda_objects_ob.
  simpl. unf.
  intro c.
  apply funextsec.
  intro f.
  apply precategory_id_right.
  intros a b c f g.
  apply precategory_fun_fun_eq.
  unf.
  unfold yoneda_morphisms_data, yoneda_objects_ob.
  simpl. unf.
  intro d.
  apply funextsec.
  intro h.
  apply precategory_assoc.
Qed.

Definition yoneda (C : precategory) : precategory_objects [C, [C^op, HSET]] :=
   tpair _ _ (is_precategory_fun_yoneda C).


  


















