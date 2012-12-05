Add Rec LoadPath "../Generalities".
Add Rec LoadPath "../hlevel1".
Add Rec LoadPath "../hlevel2".

Require Import basic_lemmas_which_should_be_in_uu0.
Require Import uu0.
Require Import hSet.
Require Import precategories.
Require Import catqalg.

Notation "a == b" := (paths a b) (at level 70, no associativity).
Notation "! p " := (pathsinv0 p) (at level 50).
Notation "p @ q" := (pathscomp0 p q) (at level 60, right associativity).

(** * Quasi-algebraic category from a setcategory *)

(** ** Objects, morphisms, identity *)

Definition cell_data_from_setcategory (C : setcategory) : cell_data.
Proof. 
  exists (dirprodpair (setcategory_objects_set C) 
                      (setcategory_total_morphisms_set C)).
  simpl; split.
  exact (dirprodpair (precategory_source C)(precategory_target C)).
  exact (precategory_total_id C).
Defined.

(** ** Composition *)

Definition catqalg_data_from_setcategory (C : setcategory) : catqalg_data :=
   tpair _ (cell_data_from_setcategory C) (precategory_total_comp C).

Lemma catqalg_data_from_setcat_id_source (C : setcategory) :
      forall c : catqalgobjects (catqalg_data_from_setcategory C),
         catqalgsource (catqalgid_morphism c) == c.
Proof.
  simpl;
  intro c.
  apply idpath.
Qed.

Lemma catqalg_data_from_setcat_id_target (C : setcategory) :
      forall c : catqalgobjects (catqalg_data_from_setcategory C),
         catqalgtarget (catqalgid_morphism c) == c.
Proof.
  simpl;
  intro c.
  apply idpath.
Qed.

Lemma comp_id_r_pr1 (C : setcategory) : forall 
  f : catqalgmorphisms (catqalg_data_from_setcategory C),
  pr1 (catqalgcompose (catqalgid_morphism (catqalgsource f)) f
  (pr2  (dirprodpair (catqalg_data_from_setcat_id_source C)
        (catqalg_data_from_setcat_id_target C)) (catqalgsource f))) == 
    pr1 f.
Proof.
  intro f.
  destruct f as [[a b] f].
  simpl in *. 
  apply pathsdirprod; apply idpath.
Defined.

Lemma comp_id_l_pr1 (C : setcategory) : forall 
  f : catqalgmorphisms (catqalg_data_from_setcategory C),
  pr1 (catqalgcompose f (catqalgid_morphism (catqalgtarget f))
  (!pr1  (dirprodpair (catqalg_data_from_setcat_id_source C)
         (catqalg_data_from_setcat_id_target C)) (catqalgtarget f))) == pr1 f.
Proof.
  intro f.
  destruct f as [[a b] f];
  simpl in *.
  apply idpath.
Defined.



Lemma catqalg_from_setcat_left_unit (C : setcategory):
  forall f : catqalgmorphisms (catqalg_data_from_setcategory C),
  catqalgcompose (catqalgid_morphism (catqalgsource f)) f
  (pr2  (dirprodpair (catqalg_data_from_setcat_id_source C)
        (catqalg_data_from_setcat_id_target C)) (catqalgsource f)) == f.
Proof.
  intro f.
   apply (total2_paths (comp_id_r_pr1 C f)).
   destruct f as [[a b] f];
   simpl in *.
   rewrite transportf_idpath.
   rewrite precategory_id_left.
   rewrite (precategory_eq_morphism_pi _ _ _ _ (idpath _ )).
   simpl.
   rewrite precategory_id_left.
   apply idpath.
Qed.  

Lemma catqalg_from_setcat_id_is_unit (C : setcategory) :
   catqalgidentity_is_unit (catqalg_data_from_setcategory C).
Proof.
  exists (dirprodpair (catqalg_data_from_setcat_id_source C)
                      (catqalg_data_from_setcat_id_target C)).
  split.
  intro f.
   apply (total2_paths (comp_id_r_pr1 C f)).
   destruct f as [[a b] f];
   simpl in *.
   rewrite transportf_idpath.
   rewrite precategory_id_left.
   rewrite (precategory_eq_morphism_pi _ _ _ _ (idpath _ )).
   simpl.
   rewrite precategory_id_left.
   apply idpath.
   
   intro f.
   
   apply (total2_paths (comp_id_l_pr1 C f)).
   simpl.
   destruct f as [[a b] f].
   simpl in *.
   rewrite transportf_idpath.
   rewrite precategory_id_right.
   rewrite (precategory_eq_morphism_pi _ _ _ _ (idpath _ )).
   simpl.
   rewrite precategory_id_right.
   apply idpath.
Qed.
   
  
Lemma catqalg_data_from_setcat_comp_source (C : setcategory) :
forall (f g : catqalgmorphisms (catqalg_data_from_setcategory C)) 
     (H : catqalgtarget f == catqalgsource g), 
           catqalgsource (catqalgcompose f g H) == catqalgsource f.
Proof.
  simpl in *.
  intros f g H.
  destruct f as [[a b] f].
  simpl in *.
  destruct g as [[c d] g].
  apply idpath.
Qed.

Lemma catqalg_data_from_setcat_comp_target (C : setcategory) :
  forall (f g : catqalgmorphisms (catqalg_data_from_setcategory C)) 
     (H : catqalgtarget f == catqalgsource g), 
           catqalgtarget (catqalgcompose f g H) == catqalgtarget g.
Proof.
  simpl in *.
  intros f g H.
  destruct f as [[a b] f].
  simpl in *.
  destruct g as [[c d] g].
  apply idpath.
Defined.


Lemma catqalg_data_from_setcat_comp_assoc_pr1 (C : setcategory)
 (f g h : catqalgmorphisms (catqalg_data_from_setcategory C))
 (Hfg : catqalgtarget f == catqalgsource g)
 (Hgh : catqalgtarget g == catqalgsource h) :

pr1 (precategory_total_comp C f (precategory_total_comp C g h Hgh)
  (Hfg @ !catqalg_data_from_setcat_comp_source C g h Hgh)) ==
pr1 (precategory_total_comp C (precategory_total_comp C f g Hfg) h
  (catqalg_data_from_setcat_comp_target C f g Hfg @ Hgh)).
Proof.
  simpl.
  apply idpath.
Defined.


Definition catqalg_data_from_setcat_comp_assoc (C : setcategory) :
   catqalgcompose_is_assoc (catqalg_data_from_setcategory C).
Proof.
  exists (dirprodpair (catqalg_data_from_setcat_comp_source C)
                      (catqalg_data_from_setcat_comp_target C)).
  simpl; intros f g h Hfg Hgh.
  apply (total2_paths 
      (catqalg_data_from_setcat_comp_assoc_pr1 C f g h Hfg Hgh)).
  rewrite transportf_idpath.
  simpl.
  repeat rewrite precategory_assoc.
  simpl.
  destruct f as [[a b] f].
  destruct g as [[c d] g].
  destruct h as [[e e'] h].
  simpl in *.
  unfold catqalgtarget, catqalgsource in *.
  simpl in *.
  unfold precategory_source, precategory_target in *;
  simpl in *.
  destruct Hfg.
  destruct Hgh.
  simpl in *.
  repeat rewrite (precategory_eq_morphism_pi _ _ _ _ (idpath _ )).
  simpl.
  apply idpath.
Qed.


Definition catqalg_from_setcat (C : setcategory) : catqalg.
Proof.
  exists (catqalg_data_from_setcategory C).
  exists (catqalg_from_setcat_id_is_unit C).
  exact (catqalg_data_from_setcat_comp_assoc C).
Defined.

  