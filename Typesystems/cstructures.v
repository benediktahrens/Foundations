

Add Rec LoadPath "../Generalities".
Add Rec LoadPath "../hlevel1".
Add Rec LoadPath "../hlevel2".

Require Import hSet.
Require Import hnat.

Require Import setlevel_categories.
Require Import pathnotations.
Import pathnotations.PathNotations.

Print hSet.

Print isofhleveltotal2.

Record cstructure := {

  ob : nat -> hSet ;
  mor : hSet ;
  s : mor -> total2 ob ;
  t : mor -> total2 ob ;
  comp : hfp s t -> mor ; 
  id : total2 ob -> mor ;
  categorical : category (tpair isaset (total2 ob) 
           (isofhleveltotal2 2 ob isasetnat 
             (fun n : nat => pr2 (ob n)))) mor s t comp id ;
  pt : ob 0 ;
  ft : forall {n : nat}, ob (S n) -> ob n ;
  canonical : forall n, ob (S n) -> mor ;
  can_pb : forall {n : nat} (X : ob (S n)) {m : nat}
       (Y : ob m) (f : mor) 
       (HfY : s f == tpair _ m Y) 
       (HfX : t f == tpair _ n (ft X)),
        ob (S m) ;
  can_pb_map : forall {n : nat} (X : ob (S n)) {m : nat}
       (Y : ob m) (f : mor) 
       (HfY : s f == tpair _ m Y) 
       (HfX : t f == tpair _ n (ft X)),
       mor ;
  can_pb_s : forall {n : nat} (X : ob (S n)) {m : nat}
       (Y : ob m) (f : mor) 
       (HfY : s f == tpair _ m Y) 
       (HfX : t f == tpair _ n (ft X)),
       s (can_pb_map X Y f HfY HfX) == 
           tpair _ (S m) (can_pb X Y f HfY HfX) ;
  can_pb_t : forall {n : nat} (X : ob (S n)) {m : nat}
       (Y : ob m) (f : mor) 
       (HfY : s f == tpair _ m Y) 
       (HfX : t f == tpair _ n (ft X)),
        t (can_pb_map X Y f HfY HfX) == 
           tpair _ (S n) X ;
  
  ob0pt : forall X : ob 0, X == pt ;
  
  (* pt is final object *)
        
}.

Check (fun X : cstructure => ob X).