(** * Introduction. Vladimir Voevodsky . Feb. 2010 - Sep. 2011 

This is the first in the group of files which contain the (current state of) the mathematical library for theproof assistant Coq based on the Univalent Foundations. It contains some new notations for constructions defined in Coq.Init library as well as the definition of dependent sum as a record.


*)




(** Preambule. *)

Global Set Universe Polymorphism.
Global Set Asymmetric Patterns.

Unset Automatic Introduction.  (** This line has to be removed for the file to compile with Coq8.2 *)

(** Universe structure *)

Notation UUU := Set (only parsing).

Inductive empty: UUU := .
Inductive unit : UUU :=  tt : unit.
Inductive bool : UUU :=  true : bool | false : bool.

Inductive identity (A : Type) (a : A) : A -> Type :=
  identity_refl : identity _ a a.

Hint Resolve identity_refl: core.

Arguments identity {A} _ _.
Arguments identity_refl {A a} , [A] a.

Arguments identity_ind [A] a P f y i.
Arguments identity_rec [A] a P f y i.
Arguments identity_rect [A] a P f y i.

Notation paths := identity .
Notation idpath := identity_refl .

(** Coproducts . 

The coproduct of two types is introduced in Coq.Init.Datatypes by the lines:

[ Inductive sum (A B:Type) : Type :=
  | inl : A -> sum A B
  | inr : B -> sum A B. ]
*)

Notation coprod := sum .

Notation ii1fun := inl .
Notation ii2fun := inr .

Notation ii1 := inl .
Notation ii2 := inr .
Arguments ii1 [ A B ] a.
Arguments ii2 [ A B ] b.


(** Dpendent sums. 

One can not use a new record each time one needs it because the general theorems about this construction would not apply to new instances of "Record" due to the "generativity" of inductive definitions in Coq. One could use "Inductive" instead of "Record" here but using "Record" which is equivalent to "Structure" allows us later to use the mechanism of canonical structures with total2. *)

Record total2 { T: Type } ( P: T -> Type ) := tpair : forall t : T , forall tp : P t , total2 P . 

Definition pr1 { T: Type } { P : T -> Type } ( tp : total2 P ) : T := match tp with tpair t p => t end .
Definition pr2 { T: Type } { P : T -> Type } ( tp : total2 P ) : P ( pr1 tp ) := match tp as a return P ( pr1 a ) with tpair t p => p end . 





(*

(** The phantom type family ( following George Gonthier ) *)

Inductive Phant ( T : Type ) := phant : Phant T .


*)

(** The following command checks wheather the patch which modifies the universe level assignement for inductive types have been installed. With the patch it returns [ paths 0 0 : UUU ] . Without the patch it returns [ paths 0 0 : Prop ]. *)

Check (paths O O) .



(* End of the file uuu.v *)
