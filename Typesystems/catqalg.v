
Add Rec LoadPath "../Generalities".
Add Rec LoadPath "../hlevel1".
Add Rec LoadPath "../hlevel2".

(*
Require Import basic_lemmas_which_should_be_in_uu0.
*)
Require Import hSet.

(*
Require Import pathnotations.
Import pathnotations.PathNotations.
*)

Notation "a == b" := (paths a b) (at level 70, no associativity).
Notation "! p " := (pathsinv0 p) (at level 50).
Notation "p @ q" := (pathscomp0 p q) (at level 60, right associativity).


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

(** ** We define [objects], [morphisms], [source], [target], [id_morphism] of a [cell_data]

    this allows us to state composition in a readable way

    We later define coercions from quasi-alg. categories down to 
    [cell_data], allowing us to reuse the names

    giving the type of the operations explicitly avoids confusion 
    with coercion from [hSet] to [UU], as mentioned above
*)

Definition objects (X : cell_data) : hSet := pr1 (pr1 X).
Definition morphisms (X : cell_data) : hSet := pr2 (pr1 X).
Definition source {X : cell_data} : morphisms X -> objects X := pr1 (pr1 (pr2 X)).
Definition target {X : cell_data} : morphisms X -> objects X := pr2 (pr1 (pr2 X)).
Definition id_morphism {X : cell_data} : objects X -> morphisms X := pr2 (pr2 X).


Definition catqalg_data := total2 (fun X : cell_data => 
   forall f g : morphisms X, target f == source g -> morphisms X).

Definition cell_data_from_catqalg_data (X : catqalg_data) : cell_data := pr1 X.
Coercion cell_data_from_catqalg_data : catqalg_data >-> cell_data.

Definition compose { X : catqalg_data } : 
    forall f g : morphisms X, target f == source g -> morphisms X := pr2 X.

(** ** Properties for categories *)
(** *** Properties of identity maps *)
(**  To state the unit laws for identity, we need to have [cell_data] where
      identities have suitable source and target 
      

*)


Definition identity_is_unit ( X : catqalg_data ) := total2 (
   ( fun H : dirprod ( forall x : objects X, source ( id_morphism x ) == x )
                     ( forall x : objects X, target ( id_morphism x ) == x ) =>
   dirprod ( forall f : morphisms X, 
             compose (id_morphism (source f)) f (pr2 H (source f)) == f ) 
           ( forall f : morphisms X, 
             compose f (id_morphism (target f)) (!pr1 H (target f)) == f ))).


(** *** Associativity of composition *)
(**   To state associativity, we need to have [catqalg_data] where
       [source] and [target] are compatible with [compose] in the
       obvious sense *)

Definition compose_is_assoc ( X : catqalg_data ) := total2 (
   ( fun H : dirprod 
           (forall f g (H : target f == source g), source (compose f g H) == source f)
           (forall f g (H : target f == source g), target (compose f g H) == target g) =>
   forall (f g h: morphisms X) (Hfg : target f == source g)
         (Hgh : target g == source h),
      compose f (compose g h Hgh) (Hfg @ !pr1 H g h Hgh) == 
        compose (compose f g Hfg ) h (pr2 H f g Hfg @ Hgh) )).

(** *** We now package these two properties into a nice package to obtain [catqalg]s *)

Definition catqalg := total2 (
   fun X : catqalg_data => dirprod (identity_is_unit X) (compose_is_assoc X)).

Definition catqalg_data_from_catqalg (X : catqalg) : catqalg_data := pr1 X.
Coercion catqalg_data_from_catqalg : catqalg >-> catqalg_data.

(** *** Check that coercions work properly *)
Check (fun X : catqalg => @compose X).
Check (fun X : catqalg => @id_morphism X).

(** *** The next coercion closes the coercion chain from [catqalg] to [UU] *)

Coercion objects : cell_data >-> hSet.

Check (fun (X : catqalg)(x : X) => id_morphism x).

(** *** Below only notes *)


(*

Definition cell_structure := total2 (fun X : cell_data =>
   dirprod (forall x : objects X, source (id_morphism x) == x)
           (forall x : objects X, target (id_morphism x) == x) ).

Definition cell_data_from_cell_structure (X : cell_structure) : cell_data := pr1 X.
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
Definition compose {X : catqalg_data} (f g : morphisms X) (H : composable f g) :=
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
   total2 (fun H : dirprod (source_of_comp X)(target_of_comp X) => is_assoc_compose X H).

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
        compose f (id_cell X (cell_target X f)) (!pr1 H (cell_target X f) ) == f.

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
     (comp : hfp s t -> mor) (id : ob -> mor) : UU := {
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
           (transportf (fun f0 : mor => dirprod (s f0 == Y) (t f0 == pt)) H (pr2 f)) ==
        pr1 (dirprodpair (final_map_s pt pt_final Y) (final_map_t pt pt_final Y))).
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




