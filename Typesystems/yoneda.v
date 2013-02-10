
(************************************************************

Benedikt Ahrens and Chris Kapulkin
january 2013


************************************************************)


(************************************************************

Contents : Definition of the Yoneda functor 
           [yoneda(C) : [C, [C^op, HSET]]]
	
           Proof that [yoneda(C)] is fully faithful  
           
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
Require Import precategory_of_hsets.

Notation "a == b" := (paths a b) (at level 70, no associativity).
Notation "! p " := (pathsinv0 p) (at level 50).
Notation "p @ q" := (pathscomp0 p q) (at level 60, right associativity).

(*Local Notation "a --> b" := (precategory_morphisms a b)(at level 50).*)
Local Notation "'hom' C" := (precategory_morphisms (C := C)) (at level 2).
Local Notation "f ;; g" := (precategory_compose f g)(at level 50).
Notation "[ C , D ]" := (precategory_fun_precategory C D).
Local Notation "# F" := (precategory_ob_mor_fun_morphisms F)(at level 3).

Ltac pathvia b := (apply (@pathscomp0 _ _ b _ )).


(** * The opposite precategory of a precategory *)

Definition opp_precat_op_mor (C : precategory_ob_mor) : precategory_ob_mor :=
   tpair (fun ob : UU => ob -> ob -> hSet) (precategory_objects C) 
        (fun a b : precategory_objects C => hom C b a  ).

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
          (d : precategory_objects C) := hom C d c.

Definition yoneda_objects_mor (C : precategory) (c : precategory_objects C)
    (d d' : precategory_objects C) (f : hom C d  d') :
   yoneda_objects_ob C c d' -> yoneda_objects_ob C c d :=
    fun g => f ;; g.

Definition yoneda_precategory_morphisms_ob_mor_fun 
 (C : precategory) (c : precategory_objects C) :
    precategory_ob_mor_fun (C^op) HSET.
Proof.
  exists (yoneda_objects_ob C c).
(*  simpl.
  unf. unfold yoneda_objects_ob. unf. simpl. *)
  intros a b f g. unfold yoneda_objects_ob in *. simpl in *.
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
    (f : hom C c c') : forall a : precategory_objects C^op, 
         hom _ (yoneda_objects C c a) ( yoneda_objects C c' a) := 
            fun a g => g ;; f.

Lemma is_precategory_fun_fun_yoneda_morphisms_data (C : precategory) 
     (c c' : precategory_objects C) (f : hom C c c') :
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
   (f : hom C c c') : precategory_fun_fun (yoneda_objects C c) (yoneda_objects C c') :=
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

Definition yoneda (C : precategory) : precategory_fun C [C^op, HSET] :=
   tpair _ _ (is_precategory_fun_yoneda C).

Notation "'ob' F" := (precategory_ob_mor_fun_objects F)(at level 4).

(** ** Yoneda lemma *)

Definition yoneda_map_1 (C : precategory)(c : precategory_objects C)
   (F : precategory_fun C^op HSET) :
       hom _ (ob (yoneda C) c) F -> pr1(F c) := 
   fun h => pr1 h c (precategory_identity c).
(*
Proof.
  intro h.
  set (ha := pr1 h c).
  simpl in *.
  exact (ha (precategory_identity c)).
*)

Print is_precategory_fun_fun.

Lemma yoneda_map_2_ax (C : precategory)(c : precategory_objects C)
       (F : precategory_fun C^op HSET) (x : pr1 (F c)) :
  is_precategory_fun_fun (pr1 (ob (yoneda C) c)) F 
         (fun (d : precategory_objects C) (f : hom (C ^op) c d) => #F f x).
Proof.
 intros a b f.
  (*
  set (H:= @precategory_fun_comp _ _ F  _ _ _ g).
*)
  simpl in *.
  apply funextsec.
  unf. simpl.
  unfold yoneda_objects_ob. simpl.
  intro g.
  set (H:= @precategory_fun_comp _ _ F  _ _  b g).
  unfold precategory_fun_comp in H.
  unfold opp_precat_data in H.
  simpl in H.
  unf.
  set (H':= H f).
  set (H2 := toforallpaths _ _ _  H' x).
  apply H2.
Qed.

Definition yoneda_map_2 (C : precategory)(c : precategory_objects C)
   (F : precategory_fun C^op HSET) :
       pr1 (F c) -> hom _ (ob (yoneda C) c) F.
Proof.
  intro x.
  exists (fun d : precategory_objects C => fun f => #F f x).
  apply yoneda_map_2_ax.
Defined.

Lemma yoneda_map_1_2 (C : precategory)(c : precategory_objects C)
  (F : precategory_fun C^op HSET)
  (alpha : hom _ (ob (yoneda C) c) F) :
      yoneda_map_2 _ _ _ (yoneda_map_1 _ _ _ alpha) == alpha.
Proof.
  simpl in *.
  apply precategory_fun_fun_eq.
  intro a'. simpl.
  apply funextsec.
  intro f.
  unfold yoneda_map_1.
  simpl.
  Check #F f.
  Check alpha c.
  pathvia ((alpha c ;; #F f) (precategory_identity c)).
  apply idpath.
  set (H':= precategory_fun_fun_ax _ _ alpha  c a' f). simpl in H'.
  simpl in *.
  rewrite <- H'.
  clear H'. 
  unf. simpl.
  unfold yoneda_objects_ob in f.
  set (H' := precategory_id_right C a' c f ).
  apply maponpaths.
  apply H'.
Qed.


Lemma yoneda_map_2_1 (C : precategory) (c : precategory_objects C)
   (F : precategory_fun C^op HSET) (x : pr1 (F c)) : 
   yoneda_map_1 _ _ _ (yoneda_map_2 _ _ _ x) == x.
Proof.
  simpl.
  rewrite (precategory_fun_id _ _ F).
  apply idpath.
Qed.


Lemma yoneda_iso_sets (C : precategory) (c : precategory_objects C)
   (F : precategory_fun C^op HSET) : 
   is_precat_isomorphism (C:=HSET) (a := hom _ ((yoneda C) c) F) (b := F c)
     (yoneda_map_1 C c F).
Proof.
  exists (yoneda_map_2 C c F).
  repeat split; simpl.
  apply funextsec.
  intro alpha.
  unf.
  simpl.
  apply (yoneda_map_1_2 C c F).
  apply funextsec.
  intro x.
  unf.
  rewrite (precategory_fun_id _ _ F).
  apply idpath.
Qed.


(*    moved to precategories.v
Definition fully_faithful {C D : precategory} (F : precategory_fun C D) := 
  forall a b : precategory_objects C, 
    isweq (precategory_ob_mor_fun_morphisms F (a:=a) (b:=b)).
*)

Lemma yoneda_fully_faithful (C : precategory) : fully_faithful (yoneda C).
Proof.
  intros a b.
  simpl.
  set (H := yoneda_map_2 C b (yoneda C a)).
  set (H' := yoneda_map_2 C a (yoneda C b)).
  assert (eximio : yoneda_morphisms C a b == yoneda_map_2 C a (yoneda C b)).
  apply funextsec.
  intro f.
  simpl.
  apply precategory_fun_fun_eq.
  simpl. intro c.
  apply funextsec.
  intro g.
  apply idpath.
  rewrite eximio.
  apply (gradth _ 
      (yoneda_map_1 C a (pr1 (yoneda C) b))).
      intro bla.
      apply yoneda_map_2_1.
  intro y.
  apply yoneda_map_1_2.
Qed.


















