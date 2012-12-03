
Add Rec LoadPath "../Generalities".
Add Rec LoadPath "../hlevel1".
Add Rec LoadPath "../hlevel2".

Require Import uu0.
Require Import hProp.

Require Import pathnotations.
Import pathnotations.PathNotations.


(** * Paths in total spaces are equivalent to pairs of paths *)

(** some of the lemmas are proved for similar fibrations twice:
    once we consider fibrations over a type in universe [UU], 
    once we consider fibrations over the universe [UU] itself *)

Lemma total2_paths {A : UU} {B : A -> UU} {s s' : total2 (fun x => B x)} 
    (p : pr1 s == pr1 s') 
    (q : transportf (fun x => B x) p (pr2 s) == pr2 s') : 
               s == s'.
Proof.
  destruct s as [a b]; destruct s' as [a' b'].
  simpl in p; destruct p.
  simpl in q; destruct q.
  apply idpath.
Defined.

Lemma total2_paths_UU  {B : UU -> hProp} {s s' : total2 (fun x => B x)} 
    (p : pr1 s == pr1 s') 
    (q : transportf (fun x => B x) p (pr2 s) == pr2 s') : 
               s == s'.
Proof.
  destruct s as [a b]; destruct s' as [a' b'].
  simpl in p; destruct p.
  simpl in q; destruct q.
  apply idpath.
Defined.


Lemma total2_paths2 {A : UU} {B : A -> UU} {a1 : A} {b1 : B a1} 
    {a2 : A} {b2 : B a2} (p : a1 == a2) 
    (q : transportf (fun x => B x) p b1 == b2) : 
    tpair (fun x => B x) a1 b1 == tpair (fun x => B x) a2 b2.
Proof.
  set (H := @total2_paths _ _  
    (tpair (fun x => B x) a1 b1)(tpair (fun x => B x) a2 b2)).
  simpl in H.
  apply (H p q).
Defined.

Lemma total2_paths2_UU {B : UU -> hProp} {A A': UU} {b : B A} 
     {b' : B A'} (p : A == A') (q : transportf (fun x => B x) p b == b') : 
    tpair (fun x => B x) A b == tpair (fun x => B x) A' b'.
Proof.
  set (H := @total2_paths _ _  
     (tpair (fun x => B x) A b)(tpair (fun x => B x) A' b')).
  simpl in H.
  apply (H p q).
Defined.


Lemma base_paths {A : UU}{B : A -> UU}(a b : total2 B) :
  a == b -> pr1 a == pr1 b.
Proof.
  intro H;
  elim H.
  apply idpath.
Defined.

Lemma base_paths_UU {B : UU -> hProp}(a b : total2 B) :
  a == b -> pr1 a == pr1 b.
Proof.
  intro H.
  apply (maponpaths  (@pr1 _ _) H).
Defined.


Definition fiber_path {B : UU -> hProp} {u v : total2 (fun x => B x)}
  (p : u == v) : transportf (fun x => B x) (base_paths_UU _ _ p) (pr2 u) == pr2 v.
Proof.
  destruct p.
  apply idpath.
Defined.

Lemma total_path_reconstruction {B : UU -> hProp} {x y : total2 (fun x => B x)} (p : x == y) :
  total2_paths_UU  _ (fiber_path p) == p.
Proof.
  induction p.
  destruct x.
  apply idpath.
Defined.


Lemma base_total_path {B : UU -> hProp} {x y : total2 (fun x => B x)}
  {p : pr1 x == pr1 y} (q : transportf _ p (pr2 x) == pr2 y) :
  (base_paths_UU _ _ (total2_paths_UU _ q)) == p.
Proof.
  destruct x as [x H]. destruct y as [y K].
  simpl in p. induction p. simpl in q. induction q.
  apply idpath.
Defined.



Lemma fiber_total_path (B : UU -> hProp) (x y : total2 (fun x => B x))
  (p : pr1 x == pr1 y) (q : transportf _ p (pr2 x) == pr2 y) :
  transportf (fun p' : pr1 x == pr1 y => transportf _ p' (pr2 x) == pr2 y)
  (base_total_path q)  (fiber_path (total2_paths_UU _ q))
  == q.
Proof.
  destruct x as [x H]. destruct y as [y K].
  simpl in p. induction p. simpl in q. induction q.
  apply idpath.
Defined.





Theorem total_paths_equiv (B : UU -> hProp) (x y : total2 (fun x => B x)) :
  weq (x == y) (total2 (fun p : pr1 x == pr1 y => 
                            transportf _ p (pr2 x) == pr2 y )).
Proof.
  exists (  fun r : x == y =>  
               tpair (fun p : pr1 x == pr1 y => 
             transportf _ p (pr2 x) == pr2 y) (base_paths_UU _ _ r) (fiber_path r)).
  apply (gradth _
  (fun pq : total2 (fun p : pr1 x == pr1 y => transportf _ p (pr2 x) == pr2 y)
          => total2_paths_UU (pr1 pq) (pr2 pq))).
  intro p.
  simpl.
  apply total_path_reconstruction.
  intros [p q].
  simpl.
  set (H':= base_total_path q).
  apply ( total2_paths2 
    (B := fun p : pr1 x == pr1 y => transportf (fun x : UU => B x) p (pr2 x) 
      == pr2 y) H').
  apply fiber_total_path.
Defined.


Lemma hset_dirprod : forall A B : UU, 
          isaset A -> isaset B -> 
           forall x y : dirprod A B, forall p q : x == y, p == q.
Proof.
  intros A B HA HB x y p q.
  assert (H:= isasetdirprod _ _ HA HB).
  simpl in H.
  apply H.
Defined.

Lemma hset_total2 : forall (A : UU) (B : A -> UU), 
          isaset A -> (forall a, isaset (B a)) -> 
           forall x y : total2 B, forall p q : x == y, p == q.
Proof.
  intros A B HA HB x y p q.
  assert (H := @isofhleveltotal2 2 A B HA HB).
  apply H.
Defined.

Definition forall_isprop {X} (P : X -> UU) :
  (forall x, isaprop (P x)) -> isaprop (forall x, P x).
Proof.
  intros H. 
  apply invproofirrelevance.
  intros x x'.
  apply funextsec.
  intro t.
  apply proofirrelevance.
  apply (H t).
Defined.


Definition isaset_if_isofhlevel2 (X : UU) :
        isofhlevel 2 X -> isaset X := fun x => x.



Lemma isweqpr1_UU (X X' : UU) ( B : (X == X') -> hProp ) 
   ( is1 : forall z , iscontr ( B z ) ) : isweq ( @pr1 _ B ) .
Proof. intros. unfold isweq. intro y. set (isy:= is1 y). 
  apply (iscontrweqf ( ezweqpr1 B y)) . assumption. 
Defined.












