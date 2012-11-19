Add Rec LoadPath "../Generalities".
Add Rec LoadPath "../hlevel1".
Add Rec LoadPath "../hlevel2".

Require Import hSet.
Require Import hnat.

Require Import iterations.

Require Import setlevel_categories.
Require Import pathnotations.
Import pathnotations.PathNotations.


Section Bstructure_def.



Check @hfp.
About hfp.

Record Bstructure := {

 B : hset_family ;
 BB : hset_family ;

 ft : hset_fam_map B ;
 delta : map_of_families BB B ;

  T : forall (i n : nat), hfp (*(B (S n)) (B (S i + n)) (B n)*)
                (ft n) (iter _ ft (S i) n) 
       -> B (S (S i + n))
           ;

  TT : forall (i n : nat), hfp
                (ft n) 
                (funcomp (delta (i + n) )(iter _ ft (S i) n))
(*                (fun x : BB (S i + n) => iter _ ft (S i) n (delta _ x)) *)
  
              -> BB (S (S i + n)) ;

  s : forall (i n : nat), hfp
                (delta n)
                (iter _ ft (S i) (S n))

              -> B (S i + n) ;

  ss : forall (i n : nat), hfp
                 (delta n)
                 (funcomp (delta _ )
                          (iter _ ft (S i) (S n)))
              -> BB (S i + n) ;

  diag : forall n, B (S n) -> BB (S (S n)) ;


  ft_T : forall (i n : nat),
           forall YXp : hfp (ft n) (iter _ ft (S i) n),
       
             (fun i' => 
                      match i' return (hfp (ft n) (iter _ ft (S i') n) -> Type) with 
                      | 0 => fun YYY  => ft _ (T _ _ YYY) == pr1 (pr1 YYY)
                      | _ => fun _ => True
                      end) i YXp

           
}.
Check TT.


























