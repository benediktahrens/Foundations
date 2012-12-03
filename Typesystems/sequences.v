Add Rec LoadPath "../Generalities".
Add Rec LoadPath "../hlevel1".
Add Rec LoadPath "../hlevel2".


Require Import basic_lemmas_which_should_be_in_uu0.

Require Import hSet.
Require Import stnfsets.
Require Import finitesets.

Notation "a == b" := (paths a b) (at level 70, no associativity).
Notation "! p " := (pathsinv0 p) (at level 50).
Notation "p @ q" := (pathscomp0 p q) (at level 60, right associativity).


(** * Definition of sequences of terms of type [A:UU] of length [n:nat] *)
(** We define such sequences as maps from the standard finite 
    set [stn n] into [A] *)

Definition sequence (A : hSet) (n : nat) := stn n -> A.

(** Empty sequence *)

Definition empty_sequence {A} : sequence A 0 :=
  funcomp weqstn0toempty fromempty.

Lemma sequence0isempty A (l : sequence A 0) :
   l == empty_sequence.
Proof.
  apply funextfunax.
  intro x;
  destruct x as [x pr]; simpl.
  unfold natlth in pr.
  unfold natgth in pr.
  simpl in *.
  elim (nopathstruetofalse (!pr)).
Qed.

 

Definition singleton_sequence {A : hSet} (a : A) : sequence A 1 :=
     fun _ => a.


(** ** Concatenation of sequences *)

Definition sequence_concat {A : hSet} {n m : nat}
       (a : sequence A n) (a' : sequence A m) : sequence A (n + m) :=
 funcomp (invmap (weqfromcoprodofstn n m))
         (prodtofunfromcoprod (dirprodpair a a')).

Section examples.

Definition listof47 : sequence _ 4 := fun _ => 7.
Definition listof28 : sequence _ 2 := fun _ => 8.

Lemma lt36proof : natlth 3 6.
reflexivity.
Defined.

Lemma lt56proof : natlth 5 6.
reflexivity.
Defined.

Definition lt36 : stn 6.
exists 3.
apply lt36proof.
Defined.

Definition lt56 : stn 6.
exists 5.
apply lt56proof.
Defined.

Time Eval compute in (sequence_concat listof47 listof28) lt36.
Time Eval compute in (sequence_concat listof47 listof28) lt56.

End examples.


Definition sequence_cons {A:hSet} n (a : A) (l : sequence A n) :
       sequence A (S n) := sequence_concat 
   (singleton_sequence a) l.

Definition sequence_snoc {A:hSet} n (a : A) (l : sequence A n) :
       sequence A (n + 1) := sequence_concat l (singleton_sequence a).

Lemma zeroltS n : natlth 0 (S n).
Proof.
  reflexivity.
Qed.

Definition zero_stnSn {n} : stn (S n).
Proof. 
  exists 0.
  apply zeroltS.
Defined.

Lemma n_in_stn_proof n : natlth n (S n).
Proof.
  apply natlthnsn.
Qed.

Definition n_in_stn n : stn (S n).
Proof.
  exists n.
  apply n_in_stn_proof.
Defined.

Definition sequence_head {A : hSet} n (l : sequence A (S n)) : A :=
          l zero_stnSn.

Definition sequence_tail {A : hSet} n (l : sequence

Lemma sequence_Sn_iscons {A:hSet} n (l : sequence A (S n)) :
   total2 (fun H : dirprod A (sequence A n) =>
              l == sequence_cons _ (pr1 H) (pr2 H)).
Proof.
  exists (dirprodpair (l 1) (

(** *** an induction principle *)

Lemma sequence_rect :
forall (A : hSet)
         (P : forall n : nat,
              sequence A n -> UU),
       P 0 (empty_sequence) ->
       (forall (n : nat) (a : A)
          (s : sequence A n),
        P n s -> P (S n) (sequence_cons n a s)) ->
       forall (n : nat) (s : sequence A n),
       P n s
.
intros A P Pnil Pcons.
induction n.
intro s.

(** *** Concatenation with the empty sequence *)

Lemma empty_concat_seq (A : hSet) (n : nat) : forall (a : sequence A n),
    sequence_concat empty_sequence a == a.
Proof.
  induction n; intros;
  simpl.
  repeat rewrite sequence0isempty.
  rewrite (sequence0isempty _ (sequence_concat empty_sequence a)).
  reflexivity.

  
  assert (H : forall i, 
       sequence_concat empty_sequence a i == a i).
  simpl. intros. 
  unfold sequence_concat. simpl.  
  unfold funcomp.
  unfold sequence in a.
  simpl.
  unfold sumofmaps.
  simpl.
  case (invmap (weqfromcoprodofstn 0 n) i).
  apply funextfunax.

set (f := invmap (weqfromcoprodofstn n m)).
set (g := prodtofunfromcoprod (dirprodpair a a')).

exact (funcomp f g).