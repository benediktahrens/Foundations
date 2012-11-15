

Add Rec LoadPath "../Generalities".
Add Rec LoadPath "../hlevel1".
Add Rec LoadPath "../hlevel2".

Require Import hSet.
Require Import hnat.

Require Import setlevel_categories.
Require Import pathnotations.
Import pathnotations.PathNotations.


Record cstructure := {

  obj : nat -> hSet ;