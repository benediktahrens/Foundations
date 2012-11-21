Add Rec LoadPath "../Generalities".
Add Rec LoadPath "../hlevel1".
Add Rec LoadPath "../hlevel2".

Require Import hSet.
Require Import hnat.

Require Import iterations.

Require Import setlevel_categories.
Require Import pathnotations.
Import pathnotations.PathNotations.


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



























