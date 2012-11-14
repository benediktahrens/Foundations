
Add Rec LoadPath "../Generalities".
Add Rec LoadPath "../hlevel1".
Add Rec LoadPath "../hlevel2".

Require Import hSet.

Section category_definition.
 About paths.

Notation "a == b" := (paths a b) (at level 40).

Definition hfp_pair {X X' Y : UU} (f : X -> Y) (f' : X' -> Y) 
          x y (p : f' y == f x):
      hfp f f'.
exists (dirprodpair x y).
simpl.
exact p.
Defined.


Record category (ob : hSet) (mor : hSet) (s t : mor -> ob)
     (comp : hfp s t -> mor) (id : ob -> mor)
       : UU := {
  id_s : forall x : ob, s (id x) == x ;
  id_t : forall x : ob, t (id x) == x ;
  comp_s : forall fg : hfp s t, 
         s (comp fg) == s (pr1 (pr1 fg)) ;
  comp_t : forall fg : hfp s t, 
         t (comp fg) == t (pr2 (pr1 fg)) ;
  comp_id_l : forall f : mor, 
      comp (hfp_pair s t f (id (s f)) (id_t _ ) ) == f 
(*         comp (tpair (fun fg =>  (tpair _ (id (s f)) f) (id_t (s f)) ) = f *)
}.