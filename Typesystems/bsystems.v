Add Rec LoadPath "../Generalities".
Add Rec LoadPath "../hlevel1".
Add Rec LoadPath "../hlevel2".

Require Import hSet.
Require Import hnat.

Require Import pathnotations.
Import pathnotations.PathNotations.


(** *** [iter] *)
(** this function might be useful in various contexts. 
     if so, it should go somewhere else *)

Fixpoint iter { B : nat -> hSet } ( f : forall n, B (S n) -> B n ) 
      ( i : nat ) : forall n, B (i + n) -> B n :=
  match i return forall n, B (i + n) -> B n with
  | 0 => fun n x => x
  | S i' => fun n x => iter f i' n (f (i' + n) x)
  end.

(** *** B-systems *)
(**  We define B-systems in several steps:
     - [preBsystem_data] consists of two sequences of sets with father and partial.
        This intermediate step allows us to define the operations in the next step 
        in a convenient way. 
        A coercion then makes father and partial accessible from [Bsystem_data].
     - [Bsystem_data] is a [preBsystem_data] with maps 
        [BT], [BTtilde], [BS], [BStilde], [Bdelta]
     - [Bsystem] is [Bsystem_data] with axioms
*)


Definition preBsystem_data := total2 (
  fun BBtilde : dirprod (nat -> hSet) (nat -> hSet) =>
    dirprod (forall n, pr1 BBtilde ( S n) -> pr1 BBtilde n)  (* ft *)
            (forall n, pr2 BBtilde (S n) -> pr1 BBtilde (S n))). (* partial *)

Definition BB (X : preBsystem_data) : nat -> hSet := pr1 (pr1 X).
Definition Btilde (X : preBsystem_data) : nat -> hSet := pr2 (pr1 X).
Definition Bft {X : preBsystem_data} {n : nat} : BB X (S n) -> BB X n := pr1 (pr2 X) n.
Definition Bpartial {X : preBsystem_data} {n : nat} : Btilde X (S n) -> BB X (S n) :=
             pr2 (pr2 X) n.

Definition Bsystem_data := total2 (fun B : preBsystem_data =>

dirprod ( 
 dirprod (
  dirprod (forall (i n : nat) (Y : BB B (S n)) (X : BB B (S (i + n))),
                Bft Y == iter (@Bft B) (S i) n X ->  BB B (S (S i + n)))  (* T *)
          (forall (i n : nat) (Y : BB B (S n)) (s : Btilde B (S i + n)),
                Bft Y == iter (@Bft B) (S i) n (Bpartial s) -> Btilde B (S (S i + n)) (* Ttilde *)
             )
          )
         (
  dirprod (forall (i n : nat) (r : Btilde B (S n)) (X : BB B (S i + S n)),
                Bpartial r == iter (@Bft B) (S i) (S n) X ->  BB B (S (S i + n)))  (* S *)
          (forall (i n : nat) (r : Btilde B (S n)) (s : Btilde B (S i + S n)),
                Bpartial r == iter (@Bft B) (S i) (S n) (Bpartial s) -> Btilde B (S i + n) (* Stilde *)
             )
         )
        )
        (forall n, BB B (S n) -> Btilde B (S (S n))) (* delta *)
).

Definition preBsystem_data_from_Bsystem_data (B : Bsystem_data) : preBsystem_data := pr1 B.
Coercion preBsystem_data_from_Bsystem_data : Bsystem_data >-> preBsystem_data.

Definition BT {B : Bsystem_data} {i n : nat} : 
    forall (Y : BB B (S n)) (X : BB B (S i + n)),
          Bft Y == iter (@Bft B) (S i) n X ->  BB B (S (S i + n)) := pr1 (pr1 (pr1 (pr2 B))) i n.

Definition BTtilde {B : Bsystem_data} {i n : nat} : 
    forall (Y : BB B (S n)) (s : Btilde B (S i + n)),
          Bft Y == iter (@Bft B) (S i) n (Bpartial s) -> Btilde B (S (S i + n)) := pr2 (pr1 (pr1 (pr2 B))) i n.

Definition BS {B : Bsystem_data} {i n : nat} : 
    forall (r : Btilde B (S n)) (X : BB B (S i + S n)),
          Bpartial r == iter (@Bft B) (S i) (S n) X ->  BB B (S (S i + n)) := pr1 (pr2 (pr1 (pr2 B))) i n.

Definition BStilde {B : Bsystem_data} {i n : nat} : 
    forall (r : Btilde B (S n)) (s : Btilde B (S i + S n)),
          Bpartial r == iter (@Bft B) (S i) (S n) (Bpartial s) -> Btilde B (S i + n) := pr2 (pr2 (pr1 (pr2 B))) i n.



Definition Baxiom1ieq0 (B : Bsystem_data) : forall n : nat,
   forall Y X : BB B (S n), forall (H : Bft Y == Bft X), 
        Bft (BT (i:=0) Y X H) == Y.


(** here we shift by 1 (one) at each appearance of [i], in order to account for 
    "i" in the text being at least one.
*)

Definition Baxiom1ig0 (B : Bsystem_data) : forall i n : nat,
   forall Y : BB B (S n), forall X : BB B (S (S i) + n), 
   forall (H : Bft Y == iter (@Bft B) (S (S i)) n X),
        Bft (BT Y X H) == BT Y (Bft X) H.





  



Definition Bsystem_data3 (B : preBsystem_data) := forall n, BB B (S n) -> Btilde B (S (S n)).
         

  
  dirprod (forall n, BB ( S n) -> BB n) (* ft *)
          (dirprod (forall n, Btilde (S n) -> BB (S n)) (* partial *)
                   (forall (i n : nat) (Y : B (S n)) (X : B (S i + n))
                        (H :  ).




Definition Bsystem := total2 ( fun

 B : hset_family  => total2 (fun 
 BB : hset_family => total2 (fun

 ft : hset_fam_map B  =>  total2 (fun 
 delta : map_of_families BB B  => total2 (fun

  T : forall (i n : nat), hfp (*(B (S n)) (B (S i + n)) (B n)*)
                (ft n) (iter _ ft (S i) n) 
       -> B (S (S i + n))

=> total2 (fun

  TT : forall (i n : nat), hfp
                (ft n) 
                (funcomp (delta (i + n) )(iter _ ft (S i) n))
  
              -> BB (S (S i + n)) 

=> total2 (fun

  SS : forall (i n : nat), hfp
                (delta n)
                (iter _ ft (S i) (S n))

              -> B (S i + n) 

=> total2 (fun

  SSS : forall (i n : nat), hfp
                 (delta n)
                 (funcomp (delta _ )
                          (iter _ ft (S i) (S n)))
              -> BB (S i + n) 

=> total2 (fun

  diag : forall n, B (S n) -> BB (S (S n)) 

=> total2 (fun


  ft_T : forall (i n : nat),
           forall YXp : hfp (ft n) (iter _ ft (S i) n),
       
    
 

         (fun i' => 
               match i' return (hfp (ft n) (iter _ ft (S i') n) -> Type) with 
               | 0 => fun YXp' => ft _ (T _ _ YXp') == pr1 (pr1 YXp')
               | S i'' => fun YXp' => 
                         ft (S (S i'' + n)) (T (S i'') n YXp') == 
                                    T i'' n 
                                      (hfp_pair (ft n) (iter B ft (S i'') n)
                                                (pr1 (pr1 YXp'))
                                                (ft _ (pr2 (pr1 YXp')))
                                  (pr2 YXp'))
 
               end) i YXp

=> total2 (fun
  
  delta_TT : forall (i n : nat),
               forall (Ysp : hfp (ft n) 
                       (funcomp (delta _ ) (iter _ ft (S i) _ ) )),

            delta _ (TT _ _ Ysp ) == T i n 
                               
        (hfp_pair (ft n) (iter _ ft (S i) n ) (pr1 (pr1 Ysp)) 
                                          (delta _ (pr2 (pr1 Ysp)))
                                          (pr2 Ysp)                                  
        )
                                              
=> total2 (fun

  ft_SS : forall (i n : nat),
          forall (rXp : hfp (delta n) (iter _ ft (S i) (S n))), 


      ( fun i' => 
           match i' return (hfp (delta n) (iter _ ft (S i') (S n)) -> Type) with
           | 0 => fun rXp' => ft n (SS 0 n rXp') == 
                              ft _ (delta _ (pr1 (pr1 rXp')))
           | S i'' => fun rXp' => 
                  
               ft (S i'' + n) (SS (S i'') n rXp') == 
                     SS _ _ 
                         (hfp_pair (delta n)
                                   (iter _ ft (S i'') (S n) )
                                   (pr1 (pr1 rXp'))
                                   (ft _ (pr2 (pr1 rXp')))
                                   (pr2 rXp'))
                         

           end ) i rXp

=> total2 (fun
 
  delta_SSS : forall (i n : nat),
              forall (rsp : hfp (delta n) 
                                (funcomp (delta (i + S n))
                                         (iter _ ft (S i) (S n)))),
     delta _ (SSS i n rsp) == SS i n (hfp_pair (delta n) (iter _ ft (S i) (S n))
                                         (pr1 (pr1 rsp))
                                         (delta (i + S n) (pr2 (pr1 rsp))) (pr2 rsp))


=>

(*  diag_delta : *) forall (n : nat) (X : B (S n)),
          delta _ (diag _ X) == T _ _ (hfp_pair (ft _ ) 
                                                (iter _ ft 1 _ ) X X (idpath _ ))
           
))))))))))))).


Definition B (X : Bsystem) := pr1 X.
Definition BB (X : Bsystem) := pr1 (pr2 X).
Check BB.
Definition ft (X : Bsystem) := pr1 (pr2 (pr2 X)).


Section Bstructure_def.




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
  
              -> BB (S (S i + n)) 
;

  SS : forall (i n : nat), hfp
                (delta n)
                (iter _ ft (S i) (S n))

              -> B (S i + n) 
;

  SSS : forall (i n : nat), hfp
                 (delta n)
                 (funcomp (delta _ )
                          (iter _ ft (S i) (S n)))
              -> BB (S i + n) 
;

  diag : forall n, B (S n) -> BB (S (S n)) 
;


  ft_T : forall (i n : nat),
           forall YXp : hfp (ft n) (iter _ ft (S i) n),
       
    
 

         (fun i' => 
               match i' return (hfp (ft n) (iter _ ft (S i') n) -> Type) with 
               | 0 => fun YXp' => ft _ (T _ _ YXp') == pr1 (pr1 YXp')
               | S i'' => fun YXp' => 
                         ft (S (S i'' + n)) (T (S i'') n YXp') == 
                                    T i'' n 
                                      (hfp_pair (ft n) (iter B ft (S i'') n)
                                                (pr1 (pr1 YXp'))
                                                (ft _ (pr2 (pr1 YXp')))
                                  (pr2 YXp'))
 
               end) i YXp

;
  
  delta_TT : forall (i n : nat),
               forall (Ysp : hfp (ft n) 
                       (funcomp (delta _ ) (iter _ ft (S i) _ ) )),

            delta _ (TT _ _ Ysp ) == T i n 
                               
        (hfp_pair (ft n) (iter _ ft (S i) n ) (pr1 (pr1 Ysp)) 
                                          (delta _ (pr2 (pr1 Ysp)))
                                          (pr2 Ysp)                                  
        )
                                              
;

  ft_SS : forall (i n : nat),
          forall (rXp : hfp (delta n) (iter _ ft (S i) (S n))), 


      ( fun i' => 
           match i' return (hfp (delta n) (iter _ ft (S i') (S n)) -> Type) with
           | 0 => fun rXp' => ft n (SS 0 n rXp') == 
                              ft _ (delta _ (pr1 (pr1 rXp')))
           | S i'' => fun rXp' => 
                  
               ft (S i'' + n) (SS (S i'') n rXp') == 
                     SS _ _ 
                         (hfp_pair (delta n)
                                   (iter _ ft (S i'') (S n) )
                                   (pr1 (pr1 rXp'))
                                   (ft _ (pr2 (pr1 rXp')))
                                   (pr2 rXp'))
                         

           end ) i rXp

;
 
  delta_SSS : forall (i n : nat),
              forall (rsp : hfp (delta n) 
                                (funcomp (delta (i + S n))
                                         (iter _ ft (S i) (S n)))),
     delta _ (SSS i n rsp) == SS i n (hfp_pair (delta n) (iter _ ft (S i) (S n))
                                         (pr1 (pr1 rsp))
                                         (delta (i + S n) (pr2 (pr1 rsp))) (pr2 rsp))

;

  diag_delta : forall (n : nat) (X : B (S n)),
          delta _ (diag _ X) == T _ _ (hfp_pair (ft _ ) 
                                                (iter _ ft 1 _ ) X X (idpath _ ))
           
}.



























