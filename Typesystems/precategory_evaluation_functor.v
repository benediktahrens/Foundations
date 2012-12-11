Add Rec LoadPath "../Generalities".
Add Rec LoadPath "../hlevel1".
Add Rec LoadPath "../hlevel2".
Add Rec LoadPath "../Proof_of_Extensionality".

Require Import basic_lemmas_which_should_be_in_uu0.
Require Import uu0.
Require Import hProp.
Require Import hSet.
Require Import precategories.
Require Import precategory_of_hsets.


Notation "a == b" := (paths a b) (at level 70, no associativity).
Notation "! p " := (pathsinv0 p) (at level 50).
Notation "p @ q" := (pathscomp0 p q) (at level 60, right associativity).

Local Notation "a --> b" := (precategory_morphisms a b)(at level 50).
Local Notation "# F" := (precategory_ob_mor_fun_morphisms F)(at level 3).
Local Notation "f ;; g" := (precategory_compose f g)(at level 50).

Notation FUN := precategory_fun_precategory.
Notation HSET := hset_precategory.

(** C -> ((C,Set),Set) *)
(** 
      - c \mapsto (F \mapsto F c)
      - f \mapsto (F \mapsto F f)
*)

(** on an object c of C we get a functor eval(c) : (C,Set) -> Set *)

Definition eval_on_obj_obj (C : precategory) (c : precategory_objects C):
   precategory_objects (FUN C HSET) -> precategory_objects HSET :=
     fun F => pr1 F c.

Definition eval_on_obj_mor (C : precategory) (c : precategory_objects C):
   forall a b : precategory_objects (FUN C HSET),
     a --> b -> eval_on_obj_obj C c a --> eval_on_obj_obj C c b :=
    fun a b f => pr1 f c.

Definition precategory_ob_mor_fun_eval_on_obj (C : precategory) 
  (c : precategory_objects C): precategory_ob_mor_fun (FUN C HSET) HSET :=
  tpair _ (eval_on_obj_obj C c) (eval_on_obj_mor C c).

Lemma is_precategory_fun_eval_on_obj (C : precategory)
   (c : precategory_objects C) : is_precategory_fun 
    (precategory_ob_mor_fun_eval_on_obj C c).
Proof.
  repeat split; simpl.
Qed.

Definition precategory_fun_eval_on_obj (C : precategory)
  (c : precategory_objects C) : precategory_fun (FUN C HSET) HSET :=
    tpair _ _ (is_precategory_fun_eval_on_obj C c).

(** on a morphism f : c --> c' we get a natural transformation 
    eval(c) => eval(c')
*)

Definition eval_on_mor (C : precategory)(c c' : precategory_objects C)
  (f : c --> c') : precategory_fun_fun_data 
     (precategory_fun_eval_on_obj C c)
     (precategory_fun_eval_on_obj C c') := 
      fun F => # (pr1 F) f.

Lemma is_precategory_fun_fun_eval_on_mor (C : precategory)
 (c c' : precategory_objects C) (f : c --> c') :
   is_precategory_fun_fun _ _ (eval_on_mor C c c' f).
Proof.
  unfold is_precategory_fun_fun;
  simpl.
  intros F F' a.
  unfold eval_on_obj_mor; simpl.
  unfold eval_on_mor; simpl.
  assert (H := @precategory_fun_fun_ax _ _ _ _ a c c' f).
  destruct F as [F Fax]; simpl in *.
  destruct F' as [F' Fax']; simpl in *.
  destruct a as [a ax]; simpl in *.
  simpl in H.
  simpl.
  unfold eval_on_obj_obj; simpl.
  rewrite H.
  apply idpath.
Qed.
  
Definition precategory_fun_fun_eval_on_mor (C : precategory)
 (c c' : precategory_objects C) (f : c --> c') :
   precategory_fun_fun _ _ :=
   tpair _ _ (is_precategory_fun_fun_eval_on_mor C c c' f).


(** Remains to prove functoriality of eval *)

Definition precategory_eval (C : precategory):
    precategory_ob_mor_fun C (FUN (FUN C HSET) HSET) :=
  tpair _ (precategory_fun_eval_on_obj C) 
          (precategory_fun_fun_eval_on_mor C).

Lemma is_precategory_fun_precategory_eval (C : precategory) :
   is_precategory_fun (precategory_eval C).
Proof.
  split; simpl.
  intro a.
  apply precategory_fun_fun_eq.
  simpl.
  intro F. unfold eval_on_mor. 
  rewrite (precategory_fun_id _ _ F).
  apply idpath.
  
  intros a b c f g.
  simpl.
  unfold precategory_fun_fun_eval_on_mor; simpl in *.
  apply precategory_fun_fun_eq.
  simpl. unfold eval_on_mor; simpl.
  intro F. 
  rewrite (precategory_fun_comp _ _ F).
  apply idpath.
Qed.

Definition eval_is_precategory_fun (C : precategory) :
   precategory_fun _ _ := tpair _ _ (is_precategory_fun_precategory_eval C).

