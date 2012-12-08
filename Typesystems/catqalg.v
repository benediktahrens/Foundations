
Add Rec LoadPath "../Generalities".
Add Rec LoadPath "../hlevel1".
Add Rec LoadPath "../hlevel2".


Require Import basic_lemmas_which_should_be_in_uu0.

Require Import hSet.

(*
Require Import pathnotations.
Import pathnotations.PathNotations.
*)

Notation "a == b" := (paths a b) (at level 70, no associativity).
Notation "! p " := (pathsinv0 p) (at level 50).
Notation "p @ q" := (pathscomp0 p q) (at level 60, right associativity).


(** * Some remarks *)
(** 
    - for improved performance, we can opacify all equality proofs,
      since we have uip for objects and morphisms
*)



(** * Definition of a category as a quasi-algebraic structure *)

(** ** We give the definition in several steps

   the first objects we define - [cell_data] - are pairs of sets with
   source and target maps and identity map / degeneracy

   we specify the first argument of the projections explicitly in order to 
   avoid confusion with projections (coercions, actually) from [hSet] to [UU]
*)



Definition cell_data := total2
    (fun obmor : dirprod hSet hSet => 
        dirprod
           (dirprod  (@pr2 hSet _ obmor -> @pr1 hSet _ obmor)
                     (@pr2 hSet _ obmor -> @pr1 hSet _ obmor))
           (@pr1 hSet _ obmor -> @pr2 hSet _ obmor)).


(**  compute hlevel of [cell_data]: to be done

*)

(** ** We define [objects], [morphisms], [source], [target], [id_morphism] 
        of a [cell_data]

    this allows us to state composition in a readable way

    We later define coercions from quasi-alg. categories down to 
    [cell_data], allowing us to reuse the names

    giving the type of the operations explicitly avoids confusion 
    with coercion from [hSet] to [UU], as mentioned above
*)

Definition catqalgobjects (X : cell_data) : hSet := pr1 (pr1 X).
Definition catqalgmorphisms (X : cell_data) : hSet := pr2 (pr1 X).
Definition catqalgsource {X : cell_data} : catqalgmorphisms X -> 
               catqalgobjects X := pr1 (pr1 (pr2 X)).
Definition catqalgtarget {X : cell_data} : catqalgmorphisms X -> 
               catqalgobjects X := pr2 (pr1 (pr2 X)).
Definition catqalgid_morphism {X : cell_data} : catqalgobjects X -> 
               catqalgmorphisms X := pr2 (pr2 X).



Definition catqalg_data := total2 (fun X : cell_data => 
   forall f g : catqalgmorphisms X, catqalgtarget f == catqalgsource g -> 
            catqalgmorphisms X).

Definition cell_data_from_catqalg_data (X : catqalg_data) : cell_data := pr1 X.
Coercion cell_data_from_catqalg_data : catqalg_data >-> cell_data.

Definition catqalgcompose { X : catqalg_data } : 
    forall f g : catqalgmorphisms X, catqalgtarget f == catqalgsource g -> 
           catqalgmorphisms X := pr2 X.

(** Equality for data of quasi-algebraic categories *)

Lemma catqalg_data_eq_from_cell_data (C C' : catqalg_data) 
   (H : pr1 C == pr1 C') : 
  transportf
  (fun x : cell_data =>
   forall f g : catqalgmorphisms x,
   catqalgtarget f == catqalgsource g -> catqalgmorphisms x) H (pr2 C) ==
      pr2 C' -> C == C'.
Proof.
  apply (total2_paths H).
Defined.
  

(** ** Axioms for categories *)
(** *** Axioms of identity maps *)
(**  To state the unit laws for identity, we need to have [cell_data] where
      identities have suitable source and target 
      

*)


Definition catqalgidentity_is_unit ( X : catqalg_data ) := total2 (
 (fun H : dirprod 
   (forall x : catqalgobjects X, catqalgsource (catqalgid_morphism x ) == x)
   (forall x : catqalgobjects X, catqalgtarget (catqalgid_morphism x ) == x) =>
 dirprod 
   (forall f : catqalgmorphisms X, 
     catqalgcompose (catqalgid_morphism (catqalgsource f)) f 
                   (pr2 H (catqalgsource f)) == f ) 
   (forall f : catqalgmorphisms X, 
     catqalgcompose f (catqalgid_morphism (catqalgtarget f)) 
                    (!pr1 H (catqalgtarget f)) == f ))).

Lemma isaprop_catqalgidentity_is_unit (X : catqalg_data) :
  isaprop (catqalgidentity_is_unit X).
Proof.
  apply isofhleveltotal2.
  apply isofhleveldirprod.
  apply impred.
  intro t.
  apply (catqalgobjects X).
  apply impred.
  intro t.
  apply (catqalgobjects X).
  
  intro t.
  apply isofhleveldirprod.
  apply impred.
  intro f.
  apply (catqalgmorphisms X).
  apply impred.
  intro f.
  apply (catqalgmorphisms X).
Qed.


(** *** Associativity of composition *)
(**   To state associativity, we need to have [catqalg_data] where
       [source] and [target] are compatible with [compose] in the
       obvious sense *)

Definition catqalgcompose_is_assoc ( X : catqalg_data ) := total2 (
   ( fun H : dirprod 
       (forall f g (H : catqalgtarget f == catqalgsource g), 
           catqalgsource (catqalgcompose f g H) == catqalgsource f)
       (forall f g (H : catqalgtarget f == catqalgsource g), 
           catqalgtarget (catqalgcompose f g H) == catqalgtarget g) =>
   forall (f g h: catqalgmorphisms X) (Hfg : catqalgtarget f == catqalgsource g)
         (Hgh : catqalgtarget g == catqalgsource h),
      catqalgcompose f (catqalgcompose g h Hgh) (Hfg @ !pr1 H g h Hgh) == 
        catqalgcompose (catqalgcompose f g Hfg ) h (pr2 H f g Hfg @ Hgh) )).

Lemma isaprop_catqalgcompose_is_assoc ( X : catqalg_data ) :
   isaprop (catqalgcompose_is_assoc X).
Proof.
  apply isofhleveltotal2.
  apply isofhleveldirprod.
  apply impred; intro t.
  apply impred; intro t'.
  apply impred; intro H.
  apply (catqalgobjects X).
  apply impred; intro t.
  apply impred; intro t'.
  apply impred; intro H.
  apply (catqalgobjects X).
  
  intro t.
  apply impred; intro f.
  apply impred; intro g.
  apply impred; intro h.
  apply impred; intro Hfg.
  apply impred; intro Hgh.
  apply (catqalgmorphisms X).
Qed.



(** *** We now package these two axioms into 
          a nice package to obtain [catqalg]s *)

Definition catqalg := total2 (
   fun X : catqalg_data => dirprod (catqalgidentity_is_unit X) 
                                   (catqalgcompose_is_assoc X)).

Definition catqalg_data_from_catqalg (X : catqalg) : catqalg_data := pr1 X.
Coercion catqalg_data_from_catqalg : catqalg >-> catqalg_data.


Definition catqalg_id_source (C : catqalg) : 
  forall x : catqalgobjects C, catqalgsource ( catqalgid_morphism x ) == x :=
          pr1 (pr1 (pr1 (pr2 C))).

Definition catqalg_id_target (C : catqalg) : 
  forall x : catqalgobjects C, catqalgtarget ( catqalgid_morphism x ) == x :=
          pr2 (pr1 (pr1 (pr2 C))).

Definition catqalg_comp_source (C : catqalg) : 
  forall f g (H : catqalgtarget f == catqalgsource g), 
    catqalgsource (catqalgcompose f g H) == catqalgsource f :=
          pr1 (pr1 (pr2 (pr2 C))).

Definition catqalg_comp_target (C : catqalg) :
  forall f g (H : catqalgtarget f == catqalgsource g), 
    catqalgtarget (catqalgcompose f g H) == catqalgtarget g :=
          pr2 (pr1 (pr2 (pr2 C))).

Definition catqalg_id_left (C : catqalg) : 
  forall f : catqalgmorphisms C, 
             catqalgcompose (catqalgid_morphism (catqalgsource f)) f 
              (catqalg_id_target _ (catqalgsource f)) == f :=
          pr1 (pr2 (pr1 (pr2 C))).

Definition catqalg_id_right (C : catqalg) : 
   forall f : catqalgmorphisms C, 
             catqalgcompose f (catqalgid_morphism (catqalgtarget f)) 
            (! catqalg_id_source _  (catqalgtarget f)) == f :=
          pr2 (pr2 (pr1 (pr2 C))).

Definition catqalg_assoc (C : catqalg) : 
 forall (f g h: catqalgmorphisms C) (Hfg : catqalgtarget f == catqalgsource g)
         (Hgh : catqalgtarget g == catqalgsource h),
   catqalgcompose f (catqalgcompose g h Hgh) 
           (Hfg @ !catqalg_comp_source C g h Hgh) == 
     catqalgcompose (catqalgcompose f g Hfg ) h 
                (catqalg_comp_target C f g Hfg @ Hgh) 
  := pr2 (pr2 (pr2 C)).


 
(** *** Check that coercions work properly *)
Check (fun X : catqalg => @catqalgcompose X).
Check (fun X : catqalg => @catqalgid_morphism X).

(** *** The next coercion closes the coercion chain from [catqalg] to [UU] *)

Coercion catqalgobjects : cell_data >-> hSet.

Check (fun (X : catqalg)(x : X) => catqalgid_morphism x).

(** ** Criterion for two quasialgebraic categories to be equal *)

Lemma catqalg_eq_if_catqalg_data (C C' : catqalg) : 
   pr1 C == pr1 C' -> C == C'. 
Proof.
  intro H.
  apply (total2_paths H).
  apply proofirrelevance.
  apply isofhleveldirprod.
  apply isaprop_catqalgidentity_is_unit.
  apply isaprop_catqalgcompose_is_assoc.
Defined.


(*
Lemma catqalg_eq (C C' : catqalg) : C == C'.
Proof.
  assert (H : pr1 C == pr1 C').
  destruct C as [C Cax]; destruct C' as [C' Cax'];
  simpl.
  assert (H': pr1 C == pr1 C').
  destruct C as [Cpre Ccomp] ; destruct C' as [Cpre' Ccomp'];
  simpl. 
  apply (total2_paths Cpre).

Lemma catqalg_eq (C C' : catqalg) :
  forall (Hob : catqalgobjects C == catqalgobjects C'),
  forall (Hmor: catqalgmorphisms C == catqalgmorphisms C'),
  forall (
  C == C'.
*)

(** ** Proof irrelevance *)
(**   for 
        - composition, 
        - associativity, 
        - source and target of composition 
*)

Lemma catqalgobuip (C : catqalg)(a b : C)(p q : a == b) : p == q.
Proof.
  apply (uip (pr2 (catqalgobjects C))).
Qed.

Lemma catqalgpairofobuip (C : catqalg) (a b c d : C) 
        (p q : dirprod (a == b) (c == d)) : p == q.
Proof.
  assert (H : pr1 p == pr1 q).
  apply catqalgobuip.
  apply (total2_paths H).
  apply catqalgobuip.
Qed.

Lemma catqalgmoruip (C : catqalg)(f g : catqalgmorphisms C)
             (p q : f == g) : p == q.
Proof.
  apply (uip (pr2 (catqalgmorphisms C))).
Qed.

Lemma catqalgcompose_pi (C : catqalg) (f g : catqalgmorphisms C)
  (H H' : catqalgtarget f == catqalgsource g) : 
     catqalgcompose f g H == catqalgcompose f g H'.
Proof.
  apply maponpaths.
  apply catqalgobuip.
Qed.

Lemma catqalg_id_left_pi (C : catqalg) (a : C )(f : catqalgmorphisms C) 
   (H : catqalgtarget (catqalgid_morphism a) == catqalgsource f):
   catqalgcompose (catqalgid_morphism a) f H == f.
Proof.
  assert (H' : catqalgsource f == a).
  rewrite <- H.
  apply catqalg_id_target.
  destruct H'.
  rewrite <- catqalg_id_left.
  apply maponpaths.
  apply catqalgobuip.
Qed.


Lemma catqalg_id_right_pi (C : catqalg) (b : C )(f : catqalgmorphisms C) 
   (H : catqalgtarget f == catqalgsource (catqalgid_morphism b)):
   catqalgcompose f (catqalgid_morphism b) H == f.
Proof.
  assert (H' : catqalgtarget f == b).
  rewrite H.
  apply catqalg_id_source.
  destruct H'.
  assert (H2:=catqalg_id_right C f).
  rewrite <- H2.
  apply maponpaths.
  apply catqalgobuip.
Qed.




(** *** Hom notation for quasi-algebraic categories *)
(** We can actually more generally define this for [cell_data]
    Since we have a coercion down to [cell_data] from [catqalg],
    this is not more inconvenient in practice *) 

Definition catqalghom { C : cell_data } (a b : C) := total2 (
    fun f : catqalgmorphisms C =>
       dirprod (catqalgsource f == a) (catqalgtarget f == b)).

Lemma isaset_catqalghom (C : cell_data) (a b : C) : isaset (catqalghom a b).
Proof.
  change (isaset) with (isofhlevel 2).
  apply isofhleveltotal2.
  apply (pr2 (catqalgmorphisms C)).
  intro x.
  apply isofhleveldirprod.
  set (H:= pr2 (catqalgobjects C)).
  simpl in H.
  unfold isaset in H.
  apply hlevelntosn.
  apply H.
  apply hlevelntosn.
  apply (pr2 (catqalgobjects C)).
Defined.

Definition catqalghomset { C : cell_data } (a b : C) : hSet := 
   tpair _ (catqalghom a b) (isaset_catqalghom C a b).

Definition catqalgmorphism_from_catqalghom (C : cell_data) (a b : C) 
    (f : catqalghom a b) : catqalgmorphisms C := pr1 f.
Coercion catqalgmorphism_from_catqalghom : catqalghom >-> pr1hSet.

(** Lemma for comparing two morphisms in [catqalghom a b] *)

Lemma catqalghom_eq (C : catqalg) (a b : C) (f g : catqalghom a b) :
   pr1 f == pr1 g -> f == g.
Proof.
  intro H;
  apply (total2_paths H).
  apply catqalgpairofobuip.
Qed.


(** **  Identity and Composition in terms of homsets *)

Definition catqalghomid {C : catqalg} (c : C) : catqalghom c c.
Proof.
  exists (catqalgid_morphism c).
  exists (catqalg_id_source C c).
  exact (catqalg_id_target C c).
Defined.



Definition catqalghomcomp {C : catqalg} {a b c : C} : catqalghom a b -> 
     catqalghom b c -> catqalghom a c.
Proof.
  intros f g.
  exists (catqalgcompose f g (pr2 (pr2 f) @ !pr1 (pr2 g))).
  exists (catqalg_comp_source _ _ _ _ @ pr1 (pr2 f) ).
  exact (catqalg_comp_target _ _ _ _ @ pr2 (pr2 g)).
Defined.

Lemma catqalghom_id_left (C : catqalg) (a b : C) (f : catqalghom a b) :
     catqalghomcomp (catqalghomid a) f == f.
Proof.
  assert (H : pr1 (catqalghomcomp (catqalghomid a) f) == pr1 f).
  destruct f as [f [p1 p2]].
  simpl.
  apply catqalg_id_left_pi.
  apply (total2_paths H).
  apply catqalgpairofobuip.
Defined.

Lemma catqalghom_id_right (C : catqalg) (a b : C) (f : catqalghom a b) :
     catqalghomcomp f (catqalghomid b) == f.
Proof.
  assert (H : pr1 (catqalghomcomp f (catqalghomid b)) == pr1 f).
  destruct f as [f [p1 p2]].
  simpl.
  apply catqalg_id_right_pi.
  apply (total2_paths H).
  apply catqalgpairofobuip.
Qed.

Lemma catqalghom_assoc (C : catqalg) :
 forall (a b c d : C) (f : catqalghom a b) (g : catqalghom b c)
  (h : catqalghom c d),
   catqalghomcomp f (catqalghomcomp g h) ==
   catqalghomcomp (catqalghomcomp f g) h.
Proof.
  intros a b c d f g h.
  set (H:= catqalg_assoc C f g h 
       (pr2 (pr2 f) @ !pr1 (pr2 g)) (pr2 (pr2 g) @ !pr1 (pr2 h))).
  assert (HOHO : pr1 (catqalghomcomp f (catqalghomcomp g h)) == 
              pr1 (catqalghomcomp (catqalghomcomp f g) h)).
  simpl.
  apply (pathscomp0 (b:=catqalgcompose f 
             (catqalgcompose g h (pr2 (pr2 g) @ !pr1 (pr2 h)))
      ((pr2 (pr2 f) @ !pr1 (pr2 g)) @
       !catqalg_comp_source C g h (pr2 (pr2 g) @ !pr1 (pr2 h))))).
  apply maponpaths.
  apply catqalgobuip.
  
  apply (pathscomp0 (b:=catqalgcompose 
            (catqalgcompose f g (pr2 (pr2 f) @ !pr1 (pr2 g))) h
      (catqalg_comp_target C f g (pr2 (pr2 f) @ !pr1 (pr2 g)) @
       pr2 (pr2 g) @ !pr1 (pr2 h)))).
  apply H.
  apply maponpaths.
  apply catqalgobuip.
  apply (total2_paths HOHO).
  apply catqalgpairofobuip.
Qed.

(** ** Isomorphism between two equal objects *)

(*
Definition catqalgmoralongeq {C : catqalg} (a b : C)
                  (H : a == b) : catqalghom a b.
Proof.
  exists (catqalgid_morphism a).
  exists (catqalg_id_source C a).
  exact (catqalg_id_target C a @ H).
Defined.
*)

Definition catqalgmoralongeq {C : catqalg} (a b : C)
                  (H : a == b) : catqalghom a b.
Proof.
  destruct H.
  exact (catqalghomid a).
Defined.

(*
Definition catqalgmoralongeqinv {C : catqalg} (a b : C)
                  (H : a == b) : catqalghom b a.
Proof.
  exists (catqalgid_morphism a).
  exists (catqalg_id_source C a @ H).
  exact (catqalg_id_target C a).
Defined.
*)

Definition catqalgmoralongeqinv {C : catqalg} (a b : C)
                  (H : a == b) : catqalghom b a.
Proof.
  destruct H.
  exact (catqalghomid a).
Defined.

Lemma is_left_inv_catqalgmoralongeq (C : catqalg) (a b : C) (H : a == b) :
   catqalghomcomp (catqalgmoralongeqinv a b H) (catqalgmoralongeq a b H) ==
           catqalghomid b.
Proof.
  destruct H.
  apply catqalghom_id_right.
Qed.

Lemma is_right_inv_catqalgmoralongeq (C : catqalg) (a b : C) (H : a == b) :
   catqalghomcomp (catqalgmoralongeq a b H) (catqalgmoralongeqinv a b H) ==
           catqalghomid a.
Proof.
  destruct H.
  apply catqalghom_id_right.
Qed.


(** ** Final objects in quasi-algebraic categories *)

Definition isfinal_in_catqalg (C : catqalg)(pt : C) :=
     forall X : C, iscontr (catqalghom X pt).

Definition final_morphism_catqalg C pt (H : isfinal_in_catqalg C pt) X :
    catqalghom X pt :=  pr1 (H X).


(** Unicity of [final_morphism_catqalg].
      We can close by [Qed.]. *)

Lemma final_is_unique_catqalg C pt (H : isfinal_in_catqalg C pt) :
   forall X, forall f : catqalghom X pt, 
       f == final_morphism_catqalg C pt H X.
Proof.
  intros X f.
  set (H':= pr2 (H X)).
  simpl in H'.
  rewrite H'.
  rewrite (H' f).
  reflexivity.
Qed.
  



(** ** HLevel of [catqalg] *)

(** remains to be done *)  



(** * Functors: Maps between quasi-algebraic categories *)

(** *** First, maps between two terms of type [cell_data] *)

(* is_cell_data_fun *)

Definition is_cell_data_fun (C C' : cell_data)(F1 : C -> C')
         (F2 : catqalgmorphisms C -> catqalgmorphisms C') :=
   dirprod (
     dirprod (forall f, catqalgsource (F2 f) == F1 (catqalgsource f))
	     (forall f, catqalgtarget (F2 f) == F1 (catqalgtarget f))
           )
           (forall x, F2 (catqalgid_morphism x) == 
                   catqalgid_morphism (F1 x)).


Lemma isaprop_is_cell_data_fun (C C' : cell_data) (F1 : C -> C')
      (F2 : catqalgmorphisms C -> catqalgmorphisms C') : 
   isaprop (is_cell_data_fun C C' F1 F2).
Proof.
  repeat apply isofhleveldirprod;
    repeat apply impred.
  intro t; apply (pr2 (catqalgobjects C')).
  intro t; apply (pr2 (catqalgobjects C')).
  intro t; apply (pr2 (catqalgmorphisms C')).
Qed.

Definition cell_data_fun (C C' : cell_data) := total2 (
  fun F : dirprod (C -> C')
	          (catqalgmorphisms C -> catqalgmorphisms C') =>
          is_cell_data_fun C C' (pr1 F) (pr2 F)).
(*
   dirprod (
     dirprod (forall f, catqalgsource (pr2 F f) == pr1 F (catqalgsource f))
	     (forall f, catqalgtarget (pr2 F f) == pr1 F (catqalgtarget f))
           )
           (forall x, pr2 F (catqalgid_morphism x) == 
                   catqalgid_morphism (pr1 F x))).
*)


Definition catqalg_fun_obj {C C'} (F : cell_data_fun C C') :
     C -> C' := pr1 (pr1 F).

Definition catqalg_fun_mor {C C'} (F : cell_data_fun C C') :
     catqalgmorphisms C -> catqalgmorphisms C' := pr2 (pr1 F).

Local Notation "# F" := (catqalg_fun_mor F)(at level 3).

Lemma cell_data_fun_eq (C C' : cell_data)(F F': cell_data_fun C C') :
     catqalg_fun_obj F == catqalg_fun_obj F' ->
     #F == #F' -> F == F'.
Proof.
  intros H H'.
  assert (Hpr1 : pr1 F == pr1 F').
  destruct F as [F Fax]; destruct F' as [F' Fax']; simpl in *.
  destruct F as [Fob Fmor]; destruct F' as [Fob' Fmor']; simpl in *.
  unfold catqalg_fun_obj, catqalg_fun_mor in H, H'. simpl in *.
  apply pathsdirprod; assumption.
  apply (total2_paths Hpr1).
  Check (pr2 F').
  apply proofirrelevance.
  apply isaprop_is_cell_data_fun.
Defined.


Coercion catqalg_fun_obj : cell_data_fun >-> Funclass.


Definition catqalg_fun_source {C C'} (F : cell_data_fun C C') : forall f, 
    catqalgsource (#F f) ==  F (catqalgsource f) := 
        pr1 (pr1 (pr2 F)).

Definition catqalg_fun_target {C C'} (F : cell_data_fun C C') : forall f, 
    catqalgtarget (#F f) == F (catqalgtarget f) := 
        pr2 (pr1 (pr2 F)).

Definition catqalg_fun_id {C C'} (F : cell_data_fun C C') :
   forall x, #F (catqalgid_morphism x) == 
                  catqalgid_morphism (F x) := pr2 (pr2 F).




(** **** A check to see whether this works as it should *)

Definition catqalg_fun_hom {C C'} (F : cell_data_fun C C') {a b} :
         catqalghom a b -> catqalghom (F a) (F b).
Proof.
  intro f.
  exists (#F f).
  exists (catqalg_fun_source F f @ maponpaths F (pr1 (pr2 f))).
  exact (catqalg_fun_target F f @ maponpaths F (pr2 (pr2 f))).
Defined.
  
(** *** Now maps between categories as quasi-alg. structures *)
(** remains compatibility with composition, which relies on the 
    axiom that functors preserve source and target and thus
    composability *)
(**  We can make [functoralg] dependent on just the data, since its 
     definition does not rely on associativity or id morphisms *)



Definition is_catqalg_fun (C C' : catqalg_data) (F : cell_data_fun C C') :=
   forall f g (H : catqalgtarget f == catqalgsource g),
        #F (catqalgcompose f g H) == 
           catqalgcompose (#F f) (#F g)  
             (catqalg_fun_target F f @ maponpaths F H @ ! catqalg_fun_source F g).

Lemma isaprop_is_catqalg_fun (C C' : catqalg_data) (F : cell_data_fun C C') :
   isaprop (is_catqalg_fun C C' F).
Proof.
  apply impred.
  intro f.
  apply impred;
  intro g.
  apply impred;
  intro H.
  apply (pr2 (catqalgmorphisms C')).
Qed.

Definition catqalg_fun (C C' : catqalg_data) := total2 (
  fun F : cell_data_fun C C' => is_catqalg_fun C C' F).


Definition cell_data_fun_from_catqalg_fun C C' (F : catqalg_fun C C') :
       cell_data_fun C C' := pr1 F.
Coercion cell_data_fun_from_catqalg_fun : catqalg_fun >-> cell_data_fun.

Definition catqalg_fun_compose {C C'} (F : catqalg_fun C C') :
  forall f g (H : catqalgtarget f == catqalgsource g),
        #F (catqalgcompose f g H) == 
           catqalgcompose (#F f) (#F g)  
            (catqalg_fun_target F f @ maponpaths F H @ ! catqalg_fun_source F g) :=
    pr2 F.



(** Again a check in terms of homsets *)
(** Introducing (local) notation might turn this statement into something
    beautiful... *)

Lemma catqalg_fun_hom_compose (C C' : catqalg) (F : catqalg_fun C C') :
  forall a b c (f : catqalghom a b) (g : catqalghom b c),
   catqalghomcomp (catqalg_fun_hom F f) (catqalg_fun_hom F g) == 
          catqalg_fun_hom F (catqalghomcomp f g).
Proof.
  intros a b c f g.
  assert (H : pr1 (catqalghomcomp (catqalg_fun_hom F f) (catqalg_fun_hom F g)) ==
                     pr1 (catqalg_fun_hom F (catqalghomcomp f g))).
    simpl.
    rewrite catqalg_fun_compose.
    apply catqalgcompose_pi.
  
  apply (total2_paths H).
  apply catqalgpairofobuip.
Qed.
  
(** ** categorical structure of categories and functors *)
(** *** composition *)




(** we opacify the equality proofs for better performance
    and less unfolding by simpl *)

Lemma cell_data_map_comp_axioms  
     (C C' C'' : catqalg)(F : catqalg_fun C C') (F' : catqalg_fun C' C''): 
dirprod
  (dirprod
     (forall f : catqalgmorphisms C,
      catqalgsource (#F' (#F f)) == F' (F (catqalgsource f)))
     (forall f : catqalgmorphisms C,
      catqalgtarget (#F' (#F f)) == F' (F (catqalgtarget f))))
  (forall x : C,
   #F' (#F (catqalgid_morphism x)) == catqalgid_morphism (F' (F x))).
Proof.
  repeat split; simpl;
   intros;
   repeat rewrite catqalg_fun_source;
   repeat rewrite catqalg_fun_target;
   repeat rewrite catqalg_fun_id;
   reflexivity.
Qed.
   
  



Definition cell_data_fun_comp  {C C' C'' : catqalg}(F : catqalg_fun C C') 
      (F' : catqalg_fun C' C''): cell_data_fun C C''.
Proof.
  exists (dirprodpair (fun x => F' (F x)) (fun f => #F' (#F f))).
  exact (cell_data_map_comp_axioms C C' C'' F F').
Defined.

Lemma catqalg_fun_composite_compose (C C' C'' : catqalg)(F : catqalg_fun C C')
      (F' : catqalg_fun C' C''): 
 forall (f g : catqalgmorphisms C) (H : catqalgtarget f == catqalgsource g),
#(cell_data_fun_comp F F') (catqalgcompose f g H) ==
catqalgcompose (#(cell_data_fun_comp F F') f) (#(cell_data_fun_comp F F') g)
  (catqalg_fun_target (cell_data_fun_comp F F') f @
   maponpaths (cell_data_fun_comp F F') H @
   !catqalg_fun_source (cell_data_fun_comp F F') g) .
Proof.
  intros f g H.
  set (HFcomp:= catqalg_fun_compose  F).
  set (HF'comp:=catqalg_fun_compose  F').
  change (#(cell_data_fun_comp F F') (catqalgcompose f g H)) with
              (#F'(#F (catqalgcompose f g H))).
  rewrite  HFcomp.
  rewrite HF'comp.
  apply catqalgcompose_pi.
Qed.
  

Definition catqalg_fun_composite {C C' C'' : catqalg}(F : catqalg_fun C C')
      (F' : catqalg_fun C' C''): catqalg_fun C C''.
Proof.
  exists (cell_data_fun_comp  F F').
  unfold is_catqalg_fun.
  apply catqalg_fun_composite_compose.
Defined.



(** *** Identity functor *)

Lemma cell_data_map_id_axioms (C : catqalg):
dirprod
  (dirprod
     (forall f : catqalgmorphisms C, catqalgsource f == catqalgsource f)
     (forall f : catqalgmorphisms C, catqalgtarget f == catqalgtarget f))
  (forall x : C, catqalgid_morphism x == catqalgid_morphism x).
Proof.
  repeat split; reflexivity.
Qed.


Definition cell_data_fun_id  {C : catqalg}: cell_data_fun C C.
Proof.
  exists (dirprodpair (fun x => x) (fun f => f)).
  apply cell_data_map_id_axioms.
Defined.

Lemma catqalg_fun_identity_compose (C : catqalg) : 
 forall (f g : catqalgmorphisms C) (H : catqalgtarget f == catqalgsource g),
#cell_data_fun_id (catqalgcompose f g H) ==
catqalgcompose (#cell_data_fun_id f) (#cell_data_fun_id g)
  (catqalg_fun_target cell_data_fun_id f @
   maponpaths cell_data_fun_id H @ !catqalg_fun_source cell_data_fun_id g).
Proof.
  intros f g H.
  change (#cell_data_fun_id (catqalgcompose f g H)) with
      (catqalgcompose f g H).
  change (#cell_data_fun_id f) with f.
  change (#cell_data_fun_id g) with g.
  apply catqalgcompose_pi.
Qed.

Definition catqalg_fun_identity (C : catqalg) : catqalg_fun C C.
Proof. 
  exists cell_data_fun_id.
  unfold is_catqalg_fun.
  apply catqalg_fun_identity_compose.
Defined.

(** ** Equality between two functors *)

Lemma catqalg_fun_eq_pr1 (C C' : catqalg) (F G : catqalg_fun C C'):
  (forall x, F x == G x) ->
   (forall f, #F f == #G f) -> pr1 F == pr1 G.
Proof.
  intros Hob Hmor.
  destruct F as [F Fax]; destruct G as [G Gax]; simpl in *.
  assert (H : pr1 F == pr1 G).
  destruct F as [F FF] ; destruct G as [G GG]; simpl in *.
  destruct F as [F1 F2]; destruct G as [G1 G2]; simpl in *.
  apply pathsdirprod.
  apply funextfunax; assumption.
  apply funextfunax; assumption.
  apply (total2_paths H).
  apply proofirrelevance.
  apply isaprop_is_cell_data_fun.
Defined.

Lemma catqalg_fun_eq (C C' : catqalg) (F G : catqalg_fun C C'):
  (forall x, F x == G x) ->
   (forall f, #F f == #G f) -> F == G.
Proof.
  intros Hob Hmor.
  apply (total2_paths (catqalg_fun_eq_pr1 _ _ _ _ Hob Hmor)).
  apply proofirrelevance.
  apply isaprop_is_catqalg_fun.
Defined.
  


(** ** Isomorphisms *)

Definition are_catqalg_fun_inverses {C C' : catqalg}
  (F : catqalg_fun C C') (G : catqalg_fun C' C) :=
 dirprod (catqalg_fun_composite F G == catqalg_fun_identity C)
         (catqalg_fun_composite G F == catqalg_fun_identity C').

Definition catqalg_fun_is_iso {C C' : catqalg} (F : catqalg_fun C C') := total2 (
   fun G => are_catqalg_fun_inverses F G).

Definition are_iso_catqalgs (C C' : catqalg) := total2 (
   fun F : catqalg_fun C C' => catqalg_fun_is_iso F).
   

Lemma catqalg_fun_eq_if_iso (C C' : catqalg) :
   are_iso_catqalgs C C' -> C == C'.
Proof.
  

Lemma isaprop_are_catqalg_fun_inverses (C C' : catqalg) (F : catqalg_fun C C')
     (G : catqalg_fun C' C) : isaprop (are_catqalg_fun_inverses F G).
Proof.
  apply isofhleveldirprod.
  


(** lemma that two functors are equal if they are pointwise equal on objects 
    and morphisms *)


(** *** Below only notes *)


(*

Definition cell_structure := total2 (fun X : cell_data =>
   dirprod (forall x : objects X, source (id_morphism x) == x)
           (forall x : objects X, target (id_morphism x) == x) ).

Definition cell_data_from_cell_structure (X : cell_structure) : 
           cell_data := pr1 X.
Coercion cell_data_from_cell_structure : cell_structure >-> cell_data.



Definition cell_data := total2
    (fun obmor : dirprod hSet hSet => 
        dirprod
           (dirprod (borderop (pr1 obmor)(pr2 obmor))
                 (borderop (pr1 obmor)(pr2 obmor)))
           (idop (pr1 obmor) (pr2 obmor))).

Definition cell_objects (X : cell_data) := pr1 (pr1 X).
Definition cell_morphisms (X : cell_data) := pr2 (pr1 X).
Definition cell_source (X : cell_data) := pr1 (pr1 (pr2 X)).
Definition cell_target (X : cell_data) := pr2 (pr1 (pr2 X)).
Definition id_cell (X : cell_data) := pr2 (pr2 X).

Definition is_cell_structure (X : cell_data) :=
   dirprod (forall x : cell_objects X, cell_source X (id_cell X x) == x)
           (forall x : cell_objects X, cell_target X (id_cell X x) == x) .

Definition cell_structure := total2 (fun X => is_cell_structure X).

Definition nerve2 (X : cell_data) := hfp (cell_source X) (cell_target X).

Definition catqalg_data := 
  total2 (fun X : cell_data => nerve2 X -> cell_morphisms X).

Definition comp (X : catqalg_data) := pr2 X.
Definition cell_from_cell_with_comp (X : catqalg_data) : cell_data := pr1 X.
Coercion cell_from_cell_with_comp : catqalg_data >-> cell_data.

Definition morphisms (X : catqalg_data) := cell_morphisms X.
Definition composable {X : catqalg_data} (f g : morphisms X) :=
         cell_target X f == cell_source X g.
Definition compose {X : catqalg_data} (f g : morphisms X) 
          (H : composable f g) :=
      comp X (hfp_pair (cell_source X) (cell_target X) g f H).


Definition source_of_comp (X : catqalg_data) := 
       forall f g (H : composable f g), cell_source X (compose f g H) == 
            cell_source X f.

Lemma isaprop_source_of_comp X : isaprop (source_of_comp X).
Proof.
 apply forall_isprop.
 intro x.
 apply forall_isprop.
 intro x'.
 apply forall_isprop.
 intro H.
 apply (pr2 (cell_objects X)).
Defined.
  

Definition target_of_comp (X : catqalg_data) := 
       forall f g (H : composable f g), cell_target X (compose f g H) == 
            cell_target X g.

Lemma isaprop_target_of_comp X : isaprop (target_of_comp X).
Proof.
 apply forall_isprop.
 intro x.
 apply forall_isprop.
 intro x'.
 apply forall_isprop.
 intro H.
 apply (pr2 (cell_objects X)).
Defined.
  

Definition is_assoc_compose (X : catqalg_data) 
       (H : dirprod (source_of_comp X)(target_of_comp X))
  := forall (f g h: morphisms X) (Hfg : composable f g)
         (Hgh : composable g h),
      compose f (compose g h Hgh) (Hfg @ !pr1 H g h Hgh) == 
        compose (compose f g Hfg ) h (pr2 H f g Hfg @ Hgh) .

Lemma isaprop_is_assoc_compose X H : isaprop (is_assoc_compose X H).
Proof.
  apply forall_isprop.
  intro f.
  apply forall_isprop.
  intro g.
  apply forall_isprop.
  intro h.
  apply forall_isprop.
  intro Hfg.
  apply forall_isprop.
  intro Hgh.
  apply (pr2 (cell_morphisms X)).
Defined.
  

Definition assoc_comp (X : catqalg_data) := 
   total2 (fun H : dirprod (source_of_comp X)(target_of_comp X) => 
          is_assoc_compose X H).

Lemma isaprop_assoc_comp X : isaprop (assoc_comp X).
Proof.
  apply isofhleveltotal2.
  apply isofhleveldirprod.
  apply isaprop_source_of_comp.
  apply isaprop_target_of_comp.
  intro H.
  apply isaprop_is_assoc_compose.
Defined.
  
  

Definition compose_id_right (X : catqalg_data) (H : is_cell_structure X) :=
   forall f : morphisms X, 
        compose f (id_cell X (cell_target X f)) 
              (!pr1 H (cell_target X f) ) == f.

Lemma isaprop_compose_id_right X H : isaprop (compose_id_right X H).
Proof.
  apply forall_isprop.
  intro x.
  apply (pr2 (cell_morphisms X)).
Defined.

Definition compose_id_left (X : catqalg_data) (H : is_cell_structure X) :=
 forall f : morphisms X, 
  compose (id_cell X (cell_source X f)) f (pr2 H (cell_source X f) ) == f.

Lemma isaprop_compose_id_left X H : isaprop (compose_id_left X H).
Proof.
  apply forall_isprop.
  intro x.
  apply (pr2 (cell_morphisms X)).
Defined.

Definition composition_units (X : catqalg_data) :=
  total2 (fun H : is_cell_structure X => 
          dirprod (compose_id_right X H) (compose_id_left X H)).

Lemma isaprop_composition_units X : isaprop (composition_units X).
Proof.
  apply isofhleveltotal2.
  apply isofhleveldirprod.
  apply forall_isprop.
  intro x.
  apply (pr2 (cell_objects X)).
  apply forall_isprop.
  intro x.
  apply (pr2 (cell_objects X)).

  intro H.
  apply isofhleveldirprod.
  apply isaprop_compose_id_right.
  apply isaprop_compose_id_left.
Defined.
  

Definition is_catqalg (X : catqalg_data) := 
 dirprod (assoc_comp X) (composition_units X).

Lemma is_hprop_is_catqalg X : isaprop (is_catqalg X).
Proof.
  apply isofhleveldirprod.
  apply isaprop_assoc_comp.
  apply isaprop_composition_units.
Defined.

Definition catqalg := total2 (fun X => is_catqalg X).



(*



Record category_data := {
  ob :> hSet ;
  mor : hSet ;
  s : mor -> ob ;
  t : mor -> ob ;
  comp : hfp s t -> mor ;
  id : ob -> mor
}.

Definition composables (C : category_data) :=
  hfp (*(mor C) (mor C) (ob C)*) (t C) (s C).



Record category (*C : category_data*) 
     (ob : hSet) (mor : hSet) (s t : mor -> ob)
     (comp : hfp s t -> mor) (id : ob -> mor)  := {
  id_s : forall x : ob, s (id x) == x ;
  id_t : forall x : ob, t (id x) == x ;
  comp_s : forall f g (Hfg : t f == s g),
         s (comp (hfp_pair s t g f Hfg)) == s f ;
  comp_t : forall f g (Hfg : t f == s g),
         t (comp (hfp_pair s t g f Hfg)) == t g ;
  comp_id_l : forall f : mor, 
      comp (hfp_pair s t f (id (s f)) (id_t _ ) ) == f ;
  comp_id_r : forall f : mor, 
      comp (hfp_pair s t (id (t f)) f  (! (id_s _ )) ) == f ;
  assoc : forall f g h (Hfg : t f == s g) (Hgh : t g == s h),
      comp (hfp_pair s t h (comp (hfp_pair s t g f Hfg)) 
           (comp_t _ _ _ @ Hgh) ) == 
      comp (hfp_pair s t (comp (hfp_pair s t h g Hgh)) 
            f (Hfg @ ! comp_s _ _ _ ) )
      

}.


Section limits.

Variables (ob mor : hSet) (s t : mor -> ob) 
      (comp : hfp s t -> mor) (id : ob -> mor)
   (X : category ob mor s t comp id).

Definition Hom (X Y : ob) := 
  total2 (fun f : mor => dirprod (s f == X)  (t f == Y)).

Definition mor_from_hom (X Y : ob) (f : Hom X Y) : mor := pr1 f.
Coercion mor_from_hom : Hom >-> pr1hSet. Check pr1hSet.

Record final_obj (pt : ob) := {
  final_map : forall Y : ob, mor ;
  final_map_s : forall Y, s (final_map Y) == Y ;
  final_map_t : forall Y, t (final_map Y) == pt ;
  final_unique : forall Y f, s f == Y -> 
                t f == pt -> f == final_map Y
}.
   
Section Hom_to_pt_contractible.

Variable pt : ob.
Variable pt_final : final_obj pt.

Definition finmap Y : Hom Y pt := 
   tpair (fun f : mor => dirprod (s f == Y)  (t f == pt)) 
      (final_map pt _ Y) 
  (dirprodpair (final_map_s pt _  Y)(final_map_t pt pt_final Y) ).

Lemma Hom_to_pt_contractible (Y : ob) : iscontr (Hom Y pt).
Proof.
  exists (finmap Y).
  intros f.
  assert (H : pr1 f == pr1 (finmap Y)).
  simpl.
  apply (final_unique).
  apply (pr2 f).
  apply (pr2 f).
  apply (total2_paths H).
  simpl.
  assert (H': pr1 
     (transportf (fun f0 : mor => dirprod (s f0 == Y) 
                (t f0 == pt)) H (pr2 f)) ==
    pr1 (dirprodpair (final_map_s pt pt_final Y) 
              (final_map_t pt pt_final Y))).
  simpl.
  apply uip.
  apply ob.
  apply (total2_paths H').
  
  apply uip.
  apply ob.
Defined.


End Hom_to_pt_contractible.

Record is_pullback (f g h k : mor) := {
  ttfg : t f == t g ;
  compfk : t k == s f   ;
  comphg : t h == s g ;
  sshk : s h == s k ;
  pb_square_commutes : comp (hfp_pair s t _ _ comphg) == 
                       comp (hfp_pair s t f k compfk) ;
  pb_exist : forall (t1 t2 : mor) (H : s t1 == s t2)
       (Hft1 : t t1 == s f) (Hgt2 : t t2 == s g)
   (CC :  comp (hfp_pair s t _ _ Hgt2) == comp (hfp_pair s t _ _ Hft1) ),
          Hom (s t1) (s k) ;
  pb_exist_comm_1 : forall (t1 t2 : mor) (H : s t1 == s t2)
       (Hft1 : t t1 == s f) (Hgt2 : t t2 == s g)
   (CC :  comp (hfp_pair s t _ _ Hgt2) == comp (hfp_pair s t _ _ Hft1) ),
      comp (hfp_pair s t k (pb_exist t1 t2 H Hft1 Hgt2 CC) 
         ( pr2 (pr2 (pb_exist t1 t2 H Hft1 Hgt2 CC)) ))
          == t1 ;
  pb_exist_comm_2 : forall (t1 t2 : mor) (H : s t1 == s t2)
       (Hft1 : t t1 == s f) (Hgt2 : t t2 == s g)
   (CC :  comp (hfp_pair s t _ _ Hgt2) == comp (hfp_pair s t _ _ Hft1) ),
      comp (hfp_pair s t h (pb_exist t1 t2 H Hft1 Hgt2 CC) 
         ( pr2 (pr2 (pb_exist t1 t2 H Hft1 Hgt2 CC)) @ !sshk ))
          == t2 ;
          
  pb_unique : forall Y : ob, forall t1 t2 : Hom Y (s k),
          forall (Hk : comp (hfp_pair s t k t1 (pr2 (pr2 t1)) ) == 
                comp (hfp_pair s t k t2 (pr2 (pr2 t2)) )),
          forall (Hh : comp (hfp_pair s t h t1 (pr2 (pr2 t1) @ !sshk) ) == 
                comp (hfp_pair s t h t2 (pr2 (pr2 t2)@ !sshk) )), 
          t1 == t2
       
}.

End limits.  


*)


*)




