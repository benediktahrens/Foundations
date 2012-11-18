

Add Rec LoadPath "../Generalities".
Add Rec LoadPath "../hlevel1".
Add Rec LoadPath "../hlevel2".

Require Import hSet.
Require Import hnat.

Require Import setlevel_categories.
Require Import pathnotations.
Import pathnotations.PathNotations.

About Hom.

Reserved Notation "'Ob'".

Record cstructure := {

  ob : nat -> hSet 
     where "'Ob'" := (tpair isaset (total2 ob) 
           (sigset ob isasetnat 
             (fun n : nat => pr2 (ob n)))) ;
  mor : hSet ;
  s : mor -> total2 ob ;
  t : mor -> total2 ob ;
  comp : hfp s t -> mor ; 
  id : total2 ob -> mor ;
  categorical : category Ob mor s t comp id ;
  pt : ob 0 ;
  ft : forall {n : nat}, ob (S n) -> ob n ;
  canonical : forall n (X : ob (S n)),
      Hom Ob _ s t  (tpair _ (S n) X) (tpair _ n (ft X)) ;

       (* mor ; (* refine towards HomSets*) *)
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
   
  pt_final : final_obj Ob mor s t (tpair _ 0 pt) ;

  can_pb_ft : forall {n : nat} (X : ob (S n)) {m : nat}
       (Y : ob m) (f : mor) 
       (HfY : s f == tpair _ m Y) 
       (HfX : t f == tpair _ n (ft X)),
        (tpair _ m (ft (can_pb X Y f HfY HfX)) == 
        (tpair _ m Y)) ;

  pb_condition : forall (n : nat)(X : ob (S n)) 
                m {Y : ob m}
                  (f : Hom Ob mor s t 
                (tpair _ m Y)
                (tpair _ n (ft X)) 
                ),
      is_pullback Ob _ s t comp f 
         (canonical _ X) (can_pb_map X Y f (pr1 (pr2 f)) (pr2 (pr2 f)) )
         (canonical _ (can_pb X Y f (pr1 (pr2 f)) (pr2 (pr2 f)) )) ;
         
  can_pb_id : forall n (X : ob (S n)), 
           can_pb X (ft X) (id (tpair _ n (ft X)))
             (id_s Ob mor s t comp id categorical _ )

         (id_t Ob mor s t comp id categorical _ )
           == X ;
  
  can_pb_map_id : forall n (X : ob (S n)), 
           can_pb_map X (ft X) (id (tpair _ n (ft X)))
             (id_s Ob mor s t comp id categorical _ )

         (id_t Ob mor s t comp id categorical _ )
           == id (tpair _ (S n) X) ;

  
  can_pb_comp : forall n (X : ob (S n)), 
            forall m (Y : ob m), forall k (Z : ob k),
           forall (f : mor)
         (Hsf : s f == (tpair _ m Y))
         (Htf : t f == (tpair _ n (ft X))),
           forall (g : mor)
         (Hsg : s g == (tpair _ k Z))
         (Htg : t g == (tpair _ m Y)),
    can_pb X Z (comp (hfp_pair s t f g (Htg @ !Hsf) )) 
       (comp_s Ob mor s t comp id categorical g f (Htg @ !Hsf) @ Hsg)
       (comp_t Ob mor s t comp id categorical g f (Htg @ !Hsf) @ Htf )  == 
        can_pb (can_pb X Y f Hsf Htf) Z g Hsg 
          (Htg @ !can_pb_ft X Y f Hsf Htf)
  ;       
  
  can_pb_map_comp : 
        forall n (X : ob (S n)), 
            forall m (Y : ob m), forall k (Z : ob k),
           forall (f : mor)
         (Hsf : s f == (tpair _ m Y))
         (Htf : t f == (tpair _ n (ft X))),
           forall (g : mor)
         (Hsg : s g == (tpair _ k Z))
         (Htg : t g == (tpair _ m Y)),
      
     can_pb_map X _ (comp (hfp_pair s t f g (Htg @ !Hsf) ))  
       (comp_s Ob mor s t comp id categorical g f (Htg @ !Hsf) @ Hsg)
       (comp_t Ob mor s t comp id categorical g f (Htg @ !Hsf) @ Htf)
== 
    comp 
      (hfp_pair s t 
        (can_pb_map X Y f Hsf Htf )
        (can_pb_map (can_pb X Y f Hsf Htf ) Z g Hsg 
            (Htg @  !can_pb_ft _ _ _ _ _  ))
       (can_pb_t _ _ _ _ _ @ !can_pb_s X Y f Hsf Htf ) )
     
}.


Check (fun X : cstructure => ob X).