Add Rec LoadPath "../Generalities/".

Require Export uu0.

Unset Automatic Introduction.

CoInductive tower := con : forall T : Type, ( T -> tower ) -> tower.

(** a constant tower that is T everywhere *)
CoFixpoint consttower ( T : Type ) : tower := con T ( fun t : T => consttower T ) . 

(** returning the base type and the family of towers over it *)
Definition towerbasefiber ( T : tower ) : total2 ( fun T' : Type => ( T' -> tower ) ) := 
 match T with ( con T' S' ) => tpair (fun T' : Type => ( T' -> tower )) T' S' end .  

(** projections *)
Definition towerbase ( T : tower ) : Type := pr1 ( towerbasefiber T ).  

Definition towerfiber ( T : tower ) ( t : towerbase T ) : tower := pr2 ( towerbasefiber T ) t . 

(** basefibertower = con *)
Definition basefibertower ( T : Type ) ( F : T -> tower ) : tower := con T F . 

(** *)
Definition toptower ( T : tower ) := 
   con ( total2 ( fun t' : towerbase T => towerbase ( towerfiber T t' ) ) )
         ( fun x => towerfiber ( towerfiber T ( pr1 x ) ) ( pr2 x ) ) . 

Definition stage ( n : nat ) ( T : tower ) : total2 ( fun Tn : Type => forall t : Tn , Type ) .
Proof. intro n. induction n . 

intro T.  exact ( match T with con T' S' => ( tpair (fun Tn : Type => Tn -> Type) 
       T' (fun t' : T' => towerbase ( S' t' ) ) ) end ) . 

intro T. exact ( IHn ( toptower T ) ) .  Defined. 









(* 
*** LOCAL Variables: ***
*** coq-prog-name: "/opt/local/bin/coqtop" ***
*** coq-prog-args: ("-emacs-U") ***
*** End: ***
 *)

