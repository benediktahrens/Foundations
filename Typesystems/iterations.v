Add Rec LoadPath "../Generalities".
Add Rec LoadPath "../hlevel1".
Add Rec LoadPath "../hlevel2".

Require Import hSet.
Require Import hnat.

(* Require Import setlevel_categories. *)
(* Require Import pathnotations. *)
(* Import pathnotations.PathNotations. *)


Definition hset_family := nat -> hSet.

Definition hset_fam_map (B : hset_family) :=
      forall n, B (S n) -> B n.

Section iterations.

Variable B : hset_family.
Variable f : hset_fam_map B.

Fixpoint iter (i : nat) : forall n, B (i + n) -> B n :=
  match i return forall n, B (i + n) -> B n with
  | 0 => fun n x => x
  | S i' => fun n x => iter i' n (f (i' + n) x)
  end.


End iterations.

Section maps_of_families.

Variables B1 B2 : hset_family.

Definition map_of_families := forall n, B1 (S n) -> B2 (S n).

End maps_of_families.

























