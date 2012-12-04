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

Definition cell_data_from_setcategory (C : setcategory) : cell_data.
Proof. 
  exists (dirprodpair (setcategory_objects_set C) 
                      (setcategory_total_morphisms_set C)).
  simpl; split.
  exact (dirprodpair (precategory_source C)(precategory_target C)).
  exact (precategory_total_id C).
Defined.

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

Lemma bla (C : setcategory) : forall 
  f : catqalgmorphisms (catqalg_data_from_setcategory C),
pr1 (catqalgcompose (catqalgid_morphism (catqalgsource f)) f
  (pr2
     (dirprodpair (catqalg_data_from_setcat_id_source C)
        (catqalg_data_from_setcat_id_target C)) (catqalgsource f))) == 
    pr1 f.
Proof.
  intro f.
   destruct f as [[a b] f];
         simpl in *.
     apply pathsdirprod; apply idpath.
Defined.


Definition catqalg_from_setcat_id_is_unit (C : setcategory) :
   catqalgidentity_is_unit (catqalg_data_from_setcategory C).
Proof.
  exists (dirprodpair (catqalg_data_from_setcat_id_source C)
                      (catqalg_data_from_setcat_id_target C)).
  split.
  intro f.
   apply (total2_paths (bla C f)).
   destruct f as [[a b] f];
   simpl in *.
   rewrite transportf_idpath.
   
   About transportf.
   rewrite  functtransportf. simpl.
   Search (transportf _ _ == _ ).
   rewrite idpathtransportf.
  unfold precategory_compose. simpl.
  unfold H.
  
  rewrite precategory_id_left.
  unfold precategory_eq_morphism. simpl.
  simpl in H.
  destruct H.



     unfold catqalgsource. simpl.
     unfold precategory_source; simpl.
     destruct f as [[a b] f]. simpl in *.
  assert (H : 
  apply total2_paths.
  
  Focus 2. intro f.
  unfold precategory_total_comp.
  simpl.
  destruct f as [[a b] f].
  simpl in *.
  
  apply pathsdirprod.
  apply pathsindirprod.

               



