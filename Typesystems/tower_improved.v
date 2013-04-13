Add Rec LoadPath  "../Generalities/".

Require Export uu0.

Unset Automatic Introduction.


(* The type of towers of types. *)

Section tower_def.

Variable TT : Type.

CoInductive tower := towerconstr : forall T0 : Type, ( T0 -> tower ) -> tower .

(* e.g. CoFixpoint consttower ( T : Type ) : tower := 
  towerconstr T ( fun t : T => consttower T ) . *)

Definition towerbasefiber ( T : tower ) : total2 (fun T' : Type => T' -> tower) := 
  match T with ( towerconstr T' S' ) => 
        tpair (fun T' : Type => ( T' -> tower )) T' S' end .  

Definition towerbase ( T : tower ) : Type := pr1 ( towerbasefiber T ).  

Definition toweroverbase { T : tower } ( t : towerbase T ) : tower := 
   pr2 ( towerbasefiber T ) t . 

Definition towerstage ( n : nat ) ( T : tower ) : 
      total2 ( fun Tn : Type => forall t : Tn , tower ) .
Proof. 
  intro n. 
  induction n . 
  intro T.  
  exact ( towerbasefiber T ) . 

  intro T.
  exists ( total2 ( fun x : pr1 ( IHn T ) => towerbase ( pr2 ( IHn T ) x ) ) ).  
  intro x .
  exact (toweroverbase (pr2 x)).
(*  destruct x as [ xn G ] . 
  exact ( toweroverbase G ) .   
*)
Defined.

Fixpoint towerstage' (n : nat) : tower -> 
    total2 (fun Tn : Type => forall t : Tn , tower) :=
 match n with
 | 0 => fun T => towerbasefiber T
 | S n' => fun T => tpair (fun Tn : Type => forall t : Tn , tower)
   (total2 (fun x : pr1 (towerstage' n' T) => towerbase (pr2 (towerstage' n' T) x))) 
   (fun x => toweroverbase (pr2 x))
 end.

Print towerstage. 

Definition towerfloor ( n : nat ) ( T : tower ) : Type := pr1 (towerstage n T).

Definition towerfather {n : nat} {T : tower} (x : towerfloor (S n) T) :
    towerfloor n T := pr1 x.

Definition towerover { n : nat } { T : tower } (G : towerfloor n T) : tower := 
   pr2 (towerstage n T) G.

Definition towerfiber {n : nat} {T : tower} (G : towerfloor n T) := 
   towerbase (towerover G). 

(*
Definition towerfatherofextension (n : nat) (T : tower) (G : towerfloor n T)
  (Y : towerfiber G) : paths (towerfather (tpair _ Y G)) G .
*)
Definition towerfibertotowerfloor { n : nat } { T : tower } ( G : towerfloor n T ) 
   ( G' : towerfiber G ) : towerfloor ( S n ) T := tpair _ G G' .

Lemma towerfatherofextension (n : nat) (T : tower) (G : towerfloor n T)
  (Y : towerfiber G) : paths (towerfather (towerfibertotowerfloor G Y)) G .
Proof.
  intros.
  apply idpath.
Qed.



(* Functions berween towers *)

CoInductive towerfun : forall  T T' : tower, Type := 
   towerfunconstr : forall ( T T' : tower ) ( f0 : towerbase T -> towerbase T' ) 
  ( ff : forall t0 : towerbase T , towerfun ( toweroverbase t0 ) 
        ( toweroverbase ( f0 t0 ) ) ) , towerfun T T' . 

CoFixpoint toweridfun ( T : tower ) : towerfun T T := 
 towerfunconstr T T ( fun x => x ) ( fun t0 => toweridfun ( toweroverbase t0 ) ) . 
 
Definition towerfunonbase { T T' : tower } ( f : towerfun T T' ) : 
       towerbase T -> towerbase T' .
Proof. 
  intros T1 T2 f G .
  destruct f as [ T T' f0 ff ] .  
  exact ( f0 G ) . 
Defined. 

Definition towerfunontowersoverbase { T T' : tower } ( f : towerfun T T' ) 
  ( t0 : towerbase T ) : towerfun ( toweroverbase t0 ) 
  ( toweroverbase ( towerfunonbase f t0 ) ) .
Proof . 
  intros. 
  destruct f as [ T T' f0 ff ] .  
  exact ( ff t0 ) .  
Defined .

Definition towerfunover { n : nat } { T T' : tower } ( f : towerfun T T' ) : 
  total2 ( fun fn : towerfloor n T -> towerfloor n T' => 
    forall G : towerfloor n T , towerfun ( towerover G ) ( towerover ( fn G ) ) ) . 
Proof. 
  intro n . 
  induction n . 

  intros . 
  exact ( tpair _ ( towerfunonbase f )  ( towerfunontowersoverbase f ) ) .   

  intros .  
  exists ( fun x => tpair _ (pr1 (IHn T T' f) (pr1 x)) 
   ( towerfunonbase (pr2 (IHn T T' f) (pr1 x) ) (pr2 x)) ) . 
  intro G. 
  destruct G as [ G1 G2 ] . 
  apply ( towerfunontowersoverbase  (pr2 (IHn T T' f) G1 ) G2 ) . 
Defined.

Fixpoint towerfunover' (n : nat) : forall (T T' : tower) (f : towerfun T T'),
  total2 ( fun fn : towerfloor n T -> towerfloor n T' => 
    forall G : towerfloor n T , towerfun ( towerover G ) ( towerover ( fn G ) ) ) :=
 match n return 
 forall (T T' : tower) (f : towerfun T T'),
    total2 ( fun fn : towerfloor n T -> towerfloor n T' => 
     forall G : towerfloor n T , towerfun ( towerover G ) ( towerover ( fn G ) ) ) 
 with
 | 0 => fun T T' f => tpair _ (towerfunonbase f) (towerfunontowersoverbase f)
 | S n' => fun T T' f =>
    tpair  (fun fn : towerfloor (S n') T -> towerfloor (S n') T' => 
      forall G : towerfloor (S n') T , towerfun ( towerover G ) ( towerover ( fn G))) 
       (fun x : towerfloor (S n') _ => tpair _ (pr1 (towerfunover' n' T T' f) (pr1 x)) 
      (towerfunonbase (pr2 (towerfunover' n' T T' f) (pr1 x) ) (pr2 x)))
      (fun G =>  towerfunontowersoverbase  (pr2 (towerfunover' n' T T' f) (pr1 G)) 
                    (pr2 G))
 end.


(* Some constructions related to toptower *)

Definition toptower ( T : tower ) := towerconstr 
  ( total2 ( fun t' : towerbase T => towerbase ( toweroverbase t' ) ) ) 
       ( fun x => toweroverbase ( pr2 x ) ) . 

CoFixpoint towerstrmap ( T : tower ) ( t0 : towerbase T ) : 
  towerfun ( toweroverbase t0 ) T := 
  towerfunconstr _ _ ( fun x => t0 ) 
  ( fun t1 => towerstrmap ( toweroverbase t0 ) t1 ) .   

Definition toptowertotower ( T : tower ) : towerfun ( toptower T ) T := 
  towerfunconstr ( toptower T ) T 
  ( fun t01 => @pr1 _ ( fun t' : towerbase T => towerbase ( toweroverbase t' ) ) t01) 
  ( fun t01 => towerstrmap ( toweroverbase ( pr1 t01 ) ) ( pr2 t01 ) )  . 

(* .... *)


(*
Definition toptowertotoptower { T1 T2 : tower } ( f : towerfun T1 T2 ) : 
  towerfun ( toptower T1 ) ( toptower T2 ) .
Proof .  intros . destruct f as [ T T' f0 ff1 ] . 




Definition towerfloortotowerfloor { n : nat } { T1 T2 : tower } 
   ( f : towerfun T1 T2 ) ( G : towerfloor n T1 ) : towerfloor n T2 . 


Definition towerfloorSnton ( n : nat ) ( T : tower ) : 
   towerfloor ( S n ) T -> towerfloor n T .
Proof . intro


Definition towerfloorovertofloor { m n : nat } { T : tower } ( G : towerfloor m T ) : 
  towerfloor n ( towerover G ) -> towerfloor ( m + n ) T . 
Proof. intro m . induction m . induction n .  

intros T G . exact ( fun x => G ) . 

intros T G

simpl .  intros n T .  destruct T . intro G .  unfold towerfloor in G . 
 unfold towerstage in G .  simpl in G . induction n . 

*)







(* The type of carriers of B-systems - towers together with a one step 
ramification at each floor other than the base floor. *)
(*
Notation B := towerfiberoverfloor.
*)

(*
Definition bsystemcarrier := total2 ( fun T : tower => forall ( n : nat ) 
  ( G : towerfloor n T ) ( G' : B G ) , Type ) . 
*)

Definition bsystemcarrier := total2 ( fun T : tower => forall ( n : nat ) 
  ( G : towerfloor ( S n ) T ) , Type ) . 

Definition bsystemcarriertotower ( T : bsystemcarrier ) := pr1 T .

Coercion bsystemcarriertotower : bsystemcarrier >-> tower.

Definition BT ( n : nat ) ( T : bsystemcarrier ) (G : towerfloor (S n) T) :=  pr2 T n G . 


Definition Tops ( T : bsystemcarrier ) := forall ( n : nat ) ( G : towerfloor ( S n ) T ), 
    towerfun ( towerover ( pr1 G ) ) ( towerover G ) . 
(*
Definition Ttops ( T : bsystemcarrier ) ( Top : Tops T ) := 
forall ( n m : nat ) ( G : towerfloor ( S n ) T ) ( G' : towerfloor ( S m ) ( towerover G ) ), 
            BT m (towerover G) G' -> BT ( Top G G' ) .  
*)
(*
Definition deltas ( T : tower ) := forall ( n : nat ) (    
*)

(*
Definition bsystemcarrierover { n : nat } { T : bsystemcarrier } 
  
  ( G : towerfloor n T ) := tpair _ ( towerover G )  
*)

(* Types of structures on brtowers which together form the structure of a B-system. *)

(*
Definition deltas ( T : tower ) := forall ( n : nat ) (    
*)






(* 
*** LOCAL Variables: ***
*** coq-prog-name: "/opt/local/bin/coqtop" ***
*** coq-prog-args: ("-emacs-U") ***
*** End: ***
 *)









CoInductive tower := towerconstr : forall T0 : Type, ( T0 -> tower ) -> tower .

(* e.g. CoFixpoint consttower ( T : Type ) : tower := 
  towerconstr T ( fun t : T => consttower T ) . *)

Definition towerbasefiber ( T : tower ) : total2 (fun T' : Type => T' -> tower) := 
  match T with ( towerconstr T' S' ) => 
        tpair (fun T' : Type => ( T' -> tower )) T' S' end .  

Definition towerbase ( T : tower ) : Type := pr1 ( towerbasefiber T ).  

Definition toweroverbase { T : tower } ( t : towerbase T ) : tower := 
   pr2 ( towerbasefiber T ) t . 

Definition towerstage ( n : nat ) ( T : tower ) : 
      total2 ( fun Tn : Type => forall t : Tn , tower ) .
Proof. 
  intro n. 
  induction n . 
  intro T.  
  exact ( towerbasefiber T ) . 

  intro T.
  exists ( total2 ( fun x : pr1 ( IHn T ) => towerbase ( pr2 ( IHn T ) x ) ) ).  
  intro x .
  exact (toweroverbase (pr2 x)).
(*  destruct x as [ xn G ] . 
  exact ( toweroverbase G ) .   
*)
Defined.

Fixpoint towerstage' (n : nat) : tower -> 
    total2 (fun Tn : Type => forall t : Tn , tower) :=
 match n with
 | 0 => fun T => towerbasefiber T
 | S n' => fun T => tpair (fun Tn : Type => forall t : Tn , tower)
   (total2 (fun x : pr1 (towerstage' n' T) => towerbase (pr2 (towerstage' n' T) x))) 
   (fun x => toweroverbase (pr2 x))
 end.

Print towerstage. 

Definition towerfloor ( n : nat ) ( T : tower ) : Type := pr1 (towerstage n T).

Definition towerfather {n : nat} {T : tower} (x : towerfloor (S n) T) :
    towerfloor n T := pr1 x.

Definition towerover { n : nat } { T : tower } (G : towerfloor n T) : tower := 
   pr2 (towerstage n T) G.

Definition towerfiber {n : nat} {T : tower} (G : towerfloor n T) := 
   towerbase (towerover G). 

(*
Definition towerfatherofextension (n : nat) (T : tower) (G : towerfloor n T)
  (Y : towerfiber G) : paths (towerfather (tpair _ Y G)) G .
*)
Definition towerfibertotowerfloor { n : nat } { T : tower } ( G : towerfloor n T ) 
   ( G' : towerfiber G ) : towerfloor ( S n ) T := tpair _ G G' .

Lemma towerfatherofextension (n : nat) (T : tower) (G : towerfloor n T)
  (Y : towerfiber G) : paths (towerfather (towerfibertotowerfloor G Y)) G .
Proof.
  intros.
  apply idpath.
Qed.



(* Functions berween towers *)

CoInductive towerfun : forall  T T' : tower, Type := 
   towerfunconstr : forall ( T T' : tower ) ( f0 : towerbase T -> towerbase T' ) 
  ( ff : forall t0 : towerbase T , towerfun ( toweroverbase t0 ) 
        ( toweroverbase ( f0 t0 ) ) ) , towerfun T T' . 

CoFixpoint toweridfun ( T : tower ) : towerfun T T := 
 towerfunconstr T T ( fun x => x ) ( fun t0 => toweridfun ( toweroverbase t0 ) ) . 
 
Definition towerfunonbase { T T' : tower } ( f : towerfun T T' ) : 
       towerbase T -> towerbase T' .
Proof. 
  intros T1 T2 f G .
  destruct f as [ T T' f0 ff ] .  
  exact ( f0 G ) . 
Defined. 

Definition towerfunontowersoverbase { T T' : tower } ( f : towerfun T T' ) 
  ( t0 : towerbase T ) : towerfun ( toweroverbase t0 ) 
  ( toweroverbase ( towerfunonbase f t0 ) ) .
Proof . 
  intros. 
  destruct f as [ T T' f0 ff ] .  
  exact ( ff t0 ) .  
Defined .

Definition towerfunover { n : nat } { T T' : tower } ( f : towerfun T T' ) : 
  total2 ( fun fn : towerfloor n T -> towerfloor n T' => 
    forall G : towerfloor n T , towerfun ( towerover G ) ( towerover ( fn G ) ) ) . 
Proof. 
  intro n . 
  induction n . 

  intros . 
  exact ( tpair _ ( towerfunonbase f )  ( towerfunontowersoverbase f ) ) .   

  intros .  
  exists ( fun x => tpair _ (pr1 (IHn T T' f) (pr1 x)) 
   ( towerfunonbase (pr2 (IHn T T' f) (pr1 x) ) (pr2 x)) ) . 
  intro G. 
  destruct G as [ G1 G2 ] . 
  apply ( towerfunontowersoverbase  (pr2 (IHn T T' f) G1 ) G2 ) . 
Defined.

Fixpoint towerfunover' (n : nat) : forall (T T' : tower) (f : towerfun T T'),
  total2 ( fun fn : towerfloor n T -> towerfloor n T' => 
    forall G : towerfloor n T , towerfun ( towerover G ) ( towerover ( fn G ) ) ) :=
 match n return 
 forall (T T' : tower) (f : towerfun T T'),
    total2 ( fun fn : towerfloor n T -> towerfloor n T' => 
     forall G : towerfloor n T , towerfun ( towerover G ) ( towerover ( fn G ) ) ) 
 with
 | 0 => fun T T' f => tpair _ (towerfunonbase f) (towerfunontowersoverbase f)
 | S n' => fun T T' f =>
    tpair  (fun fn : towerfloor (S n') T -> towerfloor (S n') T' => 
      forall G : towerfloor (S n') T , towerfun ( towerover G ) ( towerover ( fn G))) 
       (fun x : towerfloor (S n') _ => tpair _ (pr1 (towerfunover' n' T T' f) (pr1 x)) 
      (towerfunonbase (pr2 (towerfunover' n' T T' f) (pr1 x) ) (pr2 x)))
      (fun G =>  towerfunontowersoverbase  (pr2 (towerfunover' n' T T' f) (pr1 G)) 
                    (pr2 G))
 end.


(* Some constructions related to toptower *)

Definition toptower ( T : tower ) := towerconstr 
  ( total2 ( fun t' : towerbase T => towerbase ( toweroverbase t' ) ) ) 
       ( fun x => toweroverbase ( pr2 x ) ) . 

CoFixpoint towerstrmap ( T : tower ) ( t0 : towerbase T ) : 
  towerfun ( toweroverbase t0 ) T := 
  towerfunconstr _ _ ( fun x => t0 ) 
  ( fun t1 => towerstrmap ( toweroverbase t0 ) t1 ) .   

Definition toptowertotower ( T : tower ) : towerfun ( toptower T ) T := 
  towerfunconstr ( toptower T ) T 
  ( fun t01 => @pr1 _ ( fun t' : towerbase T => towerbase ( toweroverbase t' ) ) t01) 
  ( fun t01 => towerstrmap ( toweroverbase ( pr1 t01 ) ) ( pr2 t01 ) )  . 

(* .... *)


(*
Definition toptowertotoptower { T1 T2 : tower } ( f : towerfun T1 T2 ) : 
  towerfun ( toptower T1 ) ( toptower T2 ) .
Proof .  intros . destruct f as [ T T' f0 ff1 ] . 




Definition towerfloortotowerfloor { n : nat } { T1 T2 : tower } 
   ( f : towerfun T1 T2 ) ( G : towerfloor n T1 ) : towerfloor n T2 . 


Definition towerfloorSnton ( n : nat ) ( T : tower ) : 
   towerfloor ( S n ) T -> towerfloor n T .
Proof . intro


Definition towerfloorovertofloor { m n : nat } { T : tower } ( G : towerfloor m T ) : 
  towerfloor n ( towerover G ) -> towerfloor ( m + n ) T . 
Proof. intro m . induction m . induction n .  

intros T G . exact ( fun x => G ) . 

intros T G

simpl .  intros n T .  destruct T . intro G .  unfold towerfloor in G . 
 unfold towerstage in G .  simpl in G . induction n . 

*)







(* The type of carriers of B-systems - towers together with a one step 
ramification at each floor other than the base floor. *)
(*
Notation B := towerfiberoverfloor.
*)

(*
Definition bsystemcarrier := total2 ( fun T : tower => forall ( n : nat ) 
  ( G : towerfloor n T ) ( G' : B G ) , Type ) . 
*)

Definition bsystemcarrier := total2 ( fun T : tower => forall ( n : nat ) 
  ( G : towerfloor ( S n ) T ) , Type ) . 

Definition bsystemcarriertotower ( T : bsystemcarrier ) := pr1 T .

Coercion bsystemcarriertotower : bsystemcarrier >-> tower.

Definition BT ( n : nat ) ( T : bsystemcarrier ) (G : towerfloor (S n) T) :=  pr2 T n G . 


Definition Tops ( T : bsystemcarrier ) := forall ( n : nat ) ( G : towerfloor ( S n ) T ), 
    towerfun ( towerover ( pr1 G ) ) ( towerover G ) . 
(*
Definition Ttops ( T : bsystemcarrier ) ( Top : Tops T ) := 
forall ( n m : nat ) ( G : towerfloor ( S n ) T ) ( G' : towerfloor ( S m ) ( towerover G ) ), 
            BT m (towerover G) G' -> BT ( Top G G' ) .  
*)
(*
Definition deltas ( T : tower ) := forall ( n : nat ) (    
*)

(*
Definition bsystemcarrierover { n : nat } { T : bsystemcarrier } 
  
  ( G : towerfloor n T ) := tpair _ ( towerover G )  
*)

(* Types of structures on brtowers which together form the structure of a B-system. *)

(*
Definition deltas ( T : tower ) := forall ( n : nat ) (    
*)






(* 
*** LOCAL Variables: ***
*** coq-prog-name: "/opt/local/bin/coqtop" ***
*** coq-prog-args: ("-emacs-U") ***
*** End: ***
 *)

