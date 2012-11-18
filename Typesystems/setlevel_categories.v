
Add Rec LoadPath "../Generalities".
Add Rec LoadPath "../hlevel1".
Add Rec LoadPath "../hlevel2".

Require Import basic_lemmas_which_should_be_in_uu0.
Require Import hSet.

Require Import pathnotations.
Import pathnotations.PathNotations.

Print hfp.
Definition hfp_pair {X X' Y : UU} (f : X -> Y) (f' : X' -> Y) 
          x y (p : f' y == f x):
      hfp f f' := tpair _ (dirprodpair x y) p.


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










