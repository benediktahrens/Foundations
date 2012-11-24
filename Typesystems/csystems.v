

Add Rec LoadPath "../Generalities".
Add Rec LoadPath "../hlevel1".
Add Rec LoadPath "../hlevel2".

Require Import hSet.
Require Import hnat.

Require Import catqalg.
Require Import pathnotations.
Import pathnotations.PathNotations.


(** * Definition of C-Systems [Csystem] *)
(** Definition is given in several steps:
   - [Csystem_predata] : a [catqalg] with length [Clength], 
                          point [Cpt] and father [Cft]
   - [Csystem_data] : predata + canonical projections + 
                        data which later forms pullbacks of can. projs.
*)


(** ** Csystem-predata *)

Definition Csystem_predata := total2 ( fun C : catqalg =>
  dirprod (catqalgobjects C -> nat)
          (dirprod (catqalgobjects C)
                   (catqalgobjects C -> catqalgobjects C))).

Definition catqalg_from_csystem_predata (C : Csystem_predata) : 
      catqalg := pr1 C.
Coercion catqalg_from_csystem_predata : Csystem_predata >-> catqalg.

Definition Clength {C : Csystem_predata} : C -> nat := pr1 (pr2 C).
Definition Cpt (C : Csystem_predata) : C := pr1 (pr2 (pr2 C)).
Definition Cft {C : Csystem_predata} : C -> C := pr2 (pr2 (pr2 C)).

(** ** Pullback-data : object + morphism starting in this object *)

Definition Csystem_pb_data (C : Csystem_predata) := total2 (
  fun fstar : forall X : C, Clength X > 0 ->
                forall Y : C, forall f : catqalghom Y (Cft X), C =>
    forall (X : C) (H : Clength X > 0) (Y : C)
           (f : catqalghom Y (Cft X)), 
       catqalghom (fstar X H Y f) X).

(** ** [Csystem_data] as described above *)

Definition Csystem_data := total2 (fun C : Csystem_predata =>
   dirprod (forall X : C, catqalghom X (Cft X)) 
           (Csystem_pb_data C)).

Definition Csystem_data_from_Csystem_predata (C : Csystem_data):
  Csystem_predata := pr1 C.
Coercion Csystem_data_from_Csystem_predata : 
   Csystem_data >-> Csystem_predata.

Definition Ccanprojection {C : Csystem_data}(X : C) : 
    catqalghom X (Cft X) := pr1 (pr2 C) X.

Definition Cprojpbobject {C : Csystem_data} X (H : Clength X > 0)
         {Y} (f : catqalghom Y (Cft X)) : C :=
   pr1 (pr2 (pr2 C)) X H Y f.

Definition Cq {C : Csystem_data} (X : C) (H : Clength X > 0)
      {Y} (f : catqalghom Y (Cft X)) : catqalghom (Cprojpbobject X H f) X :=
   pr2 (pr2 (pr2 C)) X H Y f.


(** ** Axioms of a C-System *)

(* for now we are missing the pullbacks and final object *)

Definition Csystem_axioms (C : Csystem_data) :=
  dirprod (forall X : C, Clength X == 0 <-> X == Cpt C)
          (forall X : C, forall n : nat, Clength X == S n ->
                                         Clength (Cft X) == n).


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