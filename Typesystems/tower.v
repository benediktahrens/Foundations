
(** Started by Vladimir Voevodsky, continued by Ahrens and Kapulkin *)

Add Rec LoadPath "../Generalities/".
Add Rec LoadPath "../hlevel1/".
Add Rec LoadPath "../hlevel2/".
Require Export uu0.
Require Export hSet.

Unset Automatic Introduction.

CoInductive tower := con : forall T : Type, ( T -> tower ) -> tower.

(** a constant tower that is T everywhere *)
CoFixpoint consttower ( T : Type ) : tower := 
    con T ( fun t : T => consttower T ) . 

(** returning the base type and the family of towers over it *)
Definition towerbasefiber ( T : tower ) : total2 ( fun T' : Type => T' -> tower ) := 
 match T with con T' S' => tpair (fun T' : Type => ( T' -> tower )) T' S' end .  

(** projections *)
Definition towerbase ( T : tower ) : Type := pr1 ( towerbasefiber T ).  

Definition towerfiber ( T : tower ) ( t : towerbase T ) : tower := 
        pr2 ( towerbasefiber T ) t . 

(** basefibertower = con *)
Definition basefibertower ( T : Type ) ( F : T -> tower ) : tower := con T F . 

(** *)
Definition toptower ( T : tower ) := 
   con ( total2 ( fun t' : towerbase T => towerbase ( towerfiber T t' ) ) )
         ( fun x => towerfiber ( towerfiber T ( pr1 x ) ) ( pr2 x ) ) . 




Definition stage ( n : nat ) ( T : tower ) : 
       total2 ( fun Tn : Type => Tn -> Type ) .
Proof. 
  intro n. 
  induction n . 
  intro T.  
  
  destruct T as [T' S'].
  exists T'.
  exact (fun t' : T' => towerbase (S' t')).
  
  (* exact (match T with con T' S' => ( tpair (fun Tn : Type => Tn -> Type) 
       T' (fun t' : T' => towerbase ( S' t' ) ) ) end ) . *)

  intro T. 
  exact ( IHn ( toptower T ) ) .  
Defined.

Fixpoint stage' (n : nat)  {struct n} : tower -> 
         total2 (fun Tn : Type => Tn -> Type) :=
  match n return tower -> total2 (fun Tn : Type =>  Tn -> Type) with
  | 0 => fun T => tpair (fun Tn : Type => forall t : Tn, Type) 
                        (towerbase T) 
                        (fun t : towerbase T => towerbase (towerfiber T t))
  | S n' => fun T => stage' n' (toptower T)
  end.
 

Definition  stage_type (n : nat) (T : tower) : Type := pr1 (stage' n T).

(** write [T n] for [stage_type n T] in comments *)
(** Type of possible context extensions of [t : T n] *)

Definition context_ext (T : tower) (n : nat) (t : stage_type n T) : Type :=
   (pr2 (stage' n T) t).

Definition father  (n : nat) (T : tower) (t : stage_type (S n) T) : 
    stage_type n T.
Proof.
  induction n.
  
  unfold stage_type.
  simpl.
  intros T x.
  exact (pr1 x).
  
  unfold stage_type in *. 
  simpl in *.
  intros T x.
  
  apply IHn.
  apply x.
Defined.

Print father.

Fixpoint father' (n : nat) : forall T : tower, stage_type (S n) T -> stage_type n T :=
  match n return forall T : tower, stage_type (S n) T -> stage_type n T with
  | 0 => fun T x => pr1 x
  | S n' => fun T x => father' n' (toptower T) x
  end.


  apply (pr1 x).
  
  unfold stage
  simpl in *.
 
  intros T n x.
  destruct x.

(* here i wanted to do something stupid, namely... *)
Definition context_ext' (T : tower) (n : nat) (t : stage_type n T) : 
   stage_type (S n) T :=
   


(** ** need the same thing for hSets *)

CoInductive stower := scon : forall T : hSet, ( T -> stower ) -> stower.

(** a constant tower that is T everywhere *)
CoFixpoint conststower ( T : hSet ) : stower := 
    scon T ( fun t : T => conststower T ) . 

(** returning the base type and the family of towers over it *)
Definition stowerbasefiber ( T : stower ) : total2 (fun T' : hSet => T' -> stower) := 
 match T with scon T' S' => tpair (fun T' : hSet => ( T' -> stower )) T' S' end .  

(** projections *)
Definition stowerbase ( T : stower ) : hSet := pr1 (stowerbasefiber T).  

Definition stowerfiber ( T : stower ) ( t : stowerbase T ) : stower := 
        pr2 ( stowerbasefiber T ) t . 

(** basefibertower = con *)
Definition basefiberstower ( T : hSet ) ( F : T -> stower ) : stower := scon T F . 

(** *)

Lemma isaset_topstowerbase (T : stower) : isaset
  (total2 ( fun t' : stowerbase T => stowerbase ( stowerfiber T t' ) )).
Proof.
  intro T.
  change isaset with (isofhlevel 2).
  apply isofhleveltotal2.
  apply (pr2 (stowerbase T)).
  intro x.
  apply (pr2 (stowerbase (stowerfiber T x))).
Qed.


Definition topstower ( T : stower ) : stower := 
   scon (hSetpair (total2 ( fun t' : stowerbase T => stowerbase ( stowerfiber T t' ) ) )
                  (isaset_topstowerbase T))
         ( fun x => stowerfiber ( stowerfiber T ( pr1 x ) ) ( pr2 x ) ) .


Definition sstage ( n : nat ) ( T : stower ) : 
       total2 ( fun Tn : hSet => forall t : Tn , hSet ) .
Proof. 
  intro n. 
  induction n . 
  intro T.  
  
  destruct T as [T' S'].
  exists T'.
  exact (fun t' => stowerbase (S' t')).
  
  (* exact (match T with con T' S' => ( tpair (fun Tn : Type => Tn -> Type) 
       T' (fun t' : T' => towerbase ( S' t' ) ) ) end ) . *)

  intro T. 
  exact ( IHn ( topstower T ) ) .  
Defined. 

Definition  sstage_type (n : nat) (T : stower) : hSet := pr1 (sstage n T).


Definition stower_objects (T : stower) : Type := total2 (fun n => sstage_type n T).







(* 
*** LOCAL Variables: ***
*** coq-prog-name: "/opt/local/bin/coqtop" ***
*** coq-prog-args: ("-emacs-U") ***
*** End: ***
 *)

