
Add Rec LoadPath "../Generalities".
Add Rec LoadPath "../hlevel1".
Add Rec LoadPath "../hlevel2".

Require Import uu0.

Require Import pathnotations.
Import pathnotations.PathNotations.

Lemma total2_paths {A : UU} {B : A -> UU} {s s' : total2 B} 
    (p : paths (pr1 s) (pr1 s')) 
    (q : paths (transportf B p (pr2 s)) (pr2 s')) : 
  paths s s'.
Proof.
destruct s as [a b]; destruct s' as [a' b'].
simpl in p; destruct p.
simpl in q; destruct q.
apply idpath.
Defined.

Lemma total2_paths2 {A : UU} {B : A -> UU} {a1 : A} {b1 : B a1} 
    {a2 : A} {b2 : B a2} (p : paths a1 a2) (q : paths (transportf B p b1) b2) : 
  paths (tpair B a1 b1) (tpair B a2 b2).
Proof.
eapply total2_paths; apply q.
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









