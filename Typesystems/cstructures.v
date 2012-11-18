

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
About is_pullback.

Record cstructure := {

  ob : nat -> hSet ;
  mor : hSet ;
  s : mor -> total2 ob ;
  t : mor -> total2 ob ;
  comp : hfp s t -> mor ; 
  id : total2 ob -> mor ;
  categorical : category (tpair isaset (total2 ob) 
           (sigset ob isasetnat 
             (fun n : nat => pr2 (ob n)))) mor s t comp id ;
  pt : ob 0 ;
  ft : forall {n : nat}, ob (S n) -> ob n ;
  canonical : forall n, ob (S n) -> mor ; (* refine towards HomSets*)
  can_pb : forall {n : nat} (X : ob (S n)) {m : nat}
       (Y : ob m) (f : mor) 
       (HfY : s f == tpair _ m Y) 
       (HfX : t f == tpair _ n (ft X)),
        ob (S m) ;
  can_pb_map : forall {n : nat} (X : ob (S n)) {m : nat}
       {Y : ob m} (f : mor) 
       (HfY : s f == tpair _ m Y) 
       (HfX : t f == tpair _ n (ft X)),
       mor ;
  can_pb_s : forall {n : nat} (X : ob (S n)) {m : nat}
       (Y : ob m) (f : mor) 
       (HfY : s f == tpair _ m Y) 
       (HfX : t f == tpair _ n (ft X)),
       s (can_pb_map X  f HfY HfX) == 
           tpair _ (S m) (can_pb X Y f HfY HfX) ;
  can_pb_t : forall {n : nat} (X : ob (S n)) {m : nat}
       (Y : ob m) (f : mor) 
       (HfY : s f == tpair _ m Y) 
       (HfX : t f == tpair _ n (ft X)),
        t (can_pb_map X  f HfY HfX) == 
           tpair _ (S n) X ;
  
  ob0pt : forall X : ob 0, X == pt ;
  
  pt_final : final_obj (tpair isaset (total2 ob) 
           (sigset ob isasetnat 
             (fun n : nat => pr2 (ob n)))) mor s t (tpair _ 0 pt) ;
  pb_condition : forall (n : nat)(X : ob (S n)) 
                m {Y : ob m}
                  (f : Hom (tpair isaset (total2 ob) 
           (sigset ob isasetnat 
             (fun n : nat => pr2 (ob n)))) mor s t 
                (tpair _ m Y)
                (tpair _ n (ft X)) 
                ),
      is_pullback 
         (tpair isaset (total2 ob) 
           (sigset ob isasetnat 
             (fun n : nat => pr2 (ob n)))) 
         _ s t comp f 
         (canonical _ X) (can_pb_map X f (pr1 (pr2 f)) (pr2 (pr2 f)) )
         (canonical _ (can_pb X Y f (pr1 (pr2 f)) (pr2 (pr2 f)) )) ;
         
  can_pb_id : forall n (X : ob (S n)), 
           can_pb X (ft X) (id (tpair _ n (ft X)))
             (id_s  
                (tpair isaset (total2 ob) 
                (sigset ob isasetnat 
               (fun n : nat => pr2 (ob n))))
                    mor s t comp id categorical _ )

         (id_t  
                (tpair isaset (total2 ob) 
                (sigset ob isasetnat 
               (fun n : nat => pr2 (ob n))))
                    mor s t comp id categorical _ )
           == X ;
  
  can_pb_map_id : forall n (X : ob (S n)), 
           can_pb_map X  (id (tpair _ n (ft X)))
             (id_s  
                (tpair isaset (total2 ob) 
                (sigset ob isasetnat 
               (fun n : nat => pr2 (ob n))))
                    mor s t comp id categorical _ )

         (id_t  
                (tpair isaset (total2 ob) 
                (sigset ob isasetnat 
               (fun n : nat => pr2 (ob n))))
                    mor s t comp id categorical _ )
           == id (tpair _ (S n) X) ;

  
  can_pb_comp : forall n (X : ob (S n)), 
            forall m (Y : 

  can_pb_map_comp : 
  
}.


Check (fun X : cstructure => ob X).