

Add Rec LoadPath "../Generalities".
Add Rec LoadPath "../hlevel1".
Add Rec LoadPath "../hlevel2".

Require Import hSet.
Require Import hnat.

Require Import catqalg.
Require Import pathnotations.
Import pathnotations.PathNotations.
Require Import basic_lemmas_which_should_be_in_uu0.

(** * Definition of C-systems *)

Definition Csystem_predata := total2 (
  fun obmor : dirprod (nat -> hSet)
                      (nat -> nat -> hSet) =>
     dirprod (forall n m, pr2 obmor n m -> pr1 obmor n) (*source*)
             (forall n m, pr2 obmor n m -> pr1 obmor m) (*target*)
).

Definition Ob (c : Csystem_predata) : nat -> hSet := pr1 (pr1 c).
Coercion Ob : Csystem_predata >-> Funclass.

Definition Mor (c : Csystem_predata) : nat -> nat -> hSet := pr2 (pr1 c).

Definition Csource {c : Csystem_predata} {n m : nat} (f : Mor c n m) : Ob c n :=
      pr1 (pr2 c) _ _ f.

Definition Ctarget {c : Csystem_predata} {n m : nat} (f : Mor c n m) : Ob c m :=
      pr2 (pr2 c) _ _ f.
    

Definition Hom {c : Csystem_predata}{n m : nat} (a : Ob c n)(b : Ob c m) : UU :=
   total2 (fun f : Mor c n m => 
              dirprod (Csource f == a)
                      (Ctarget f == b)).

Lemma isaset_Hom {C : Csystem_predata}{n m : nat} (a : Ob C n)(b : Ob C m) :
   isaset (Hom a b).
Proof.
  change (isaset) with (isofhlevel 2).
  apply isofhleveltotal2.
  apply (pr2 (Mor C n m)).
  intro x.
  apply isofhleveldirprod.
  set (H:= pr2 (Ob C n)).
  simpl in H.
  unfold isaset in H.
  apply hlevelntosn.
  apply H.
  apply hlevelntosn.
  apply (pr2 (Ob C m)).
Qed.

Lemma Hom_eq (c : Csystem_predata)(n m : nat) (a : Ob c n)(b : Ob c m) 
      (f g : Hom a b) :
   pr1 f == pr1 g -> f == g.
Proof.
  intro H;
  apply (total2_paths H).
  apply pairofobuip.
Qed.


Definition Csystem_catdata := total2 (
  fun c : Csystem_predata => dirprod
     (forall n (a : Ob c n), Hom a a)
     (forall n m k 
      (a : Ob c n) (b : Ob c m) (c : Ob c k),
      forall (f : Hom a b) (g : Hom b c), Hom a c)).

Definition Csystem_predata_from_Csystem_catdata (c : Csystem_catdata) :
    Csystem_predata := pr1 c.
Coercion Csystem_predata_from_Csystem_catdata : Csystem_catdata >-> Csystem_predata.


Definition Csystem_id {c : Csystem_catdata}{n : nat} (a : Ob c n) : Hom a a :=
            pr1 (pr2 c) _ a.

Definition Csystem_comp (C : Csystem_catdata){n m k : nat} {a : Ob C n}
    {b : Ob C m} {c : Ob C k} : Hom a b -> Hom b c -> Hom a c :=
       fun f g => pr2 (pr2 C) _ _ _ _ _ _ f g.

Notation "f ;; g" := (Csystem_comp _ f g) (at level 50).


Definition Csystem_cat := total2 (
   fun C : Csystem_catdata => dirprod 
      (dirprod (forall (n m : nat) (a : Ob C n) (b : Ob C m)
                  (f : Hom a b), Csystem_id a ;; f == f)
               (forall (n m : nat) (a : Ob C n) (b : Ob C m)
                  (f : Hom a b), f ;; Csystem_id b == f)
      )
      (forall (n m k l : nat) (a : Ob C n) (b : Ob C m) (c : Ob C k) (d : Ob C l) 
       (f : Hom a b) (g : Hom b c) (h : Hom c d), (f ;; g) ;; h == f ;; (g ;; h))).

Definition Csystem_catdata_from_Csystem_cat (C : Csystem_cat) : Csystem_catdata :=
     pr1 C.
Coercion Csystem_catdata_from_Csystem_cat : Csystem_cat >-> Csystem_catdata.

Definition comp_assoc (C : Csystem_cat) : forall (n m k l : nat) (a : Ob C n)
     (b : Ob C m) (c : Ob C k) (d : Ob C l) 
     (f : Hom a b) (g : Hom b c) (h : Hom c d), (f ;; g) ;; h == f ;; (g ;; h) :=
        pr2 (pr2 C).

Definition id_left (C : Csystem_cat) : forall (n m : nat) (a : Ob C n) (b : Ob C m)
   (f : Hom a b), Csystem_id a ;; f == f := pr1 (pr1 (pr2 C)).

Definition id_right (C : Csystem_cat) : forall (n m : nat) (a : Ob C n) (b : Ob C m)
   (f : Hom a b), f ;; Csystem_id b == f := pr2 (pr1 (pr2 C)).

Definition unique_empty (C : Csystem_catdata) := total2 (
   fun pt : Ob C 0 => forall a : Ob C 0, a == pt).

Definition Csystem_cat_pointed := total2 (
   fun C : Csystem_cat => unique_empty C).

Definition Csystem_cat_from_Csystem_cat_pointed (C : Csystem_cat_pointed) : 
    Csystem_cat := pr1 C.
Coercion Csystem_cat_from_Csystem_cat_pointed : Csystem_cat_pointed >-> Csystem_cat.

Definition Csystem_cat_pt (C : Csystem_cat_pointed) : Ob C 0 := pr1 (pr2 C).

Definition Csystem_cat_pointed_final (C : Csystem_cat_pointed) := total2 (
     fun fin_mor : forall n (a : Ob C n), Hom a (Csystem_cat_pt C) => 
            forall n (a : Ob C n) (g : Hom a (Csystem_cat_pt C)), 
                  g == fin_mor n a).

Definition Csystem_ft_projection (C : Csystem_catdata) := total2 (
   fun ft : forall n, Ob C (S n) -> Ob C n =>
      forall n (X : Ob C (S n)), Hom X (ft _ X)).

Definition Csystem_ft_proj := total2 (
   fun C : Csystem_catdata => Csystem_ft_projection C).

Definition Csystem_catdata_from_Csystem_ft_proj (C : Csystem_ft_proj) :
    Csystem_catdata := pr1 C.
Coercion Csystem_catdata_from_Csystem_ft_proj : Csystem_ft_proj >-> Csystem_catdata.

Definition Cft {C : Csystem_ft_proj} {n : nat} (X : Ob C (S n)) : Ob C n :=
    pr1 (pr2 C) n X.

Definition Cp (C : Csystem_ft_proj) {n : nat} (X : Ob C (S n)) : Hom X (Cft X) :=
   pr2 (pr2 C) n X.

Definition Csystem_star_q_data (C : Csystem_ft_proj) := total2 (
     fun star : forall (n : nat) (X : Ob C (S n)) 
              m (Y : Ob C m) (f : Hom Y (Cft X)), Ob C (S m) =>
       forall (n : nat) (X : Ob C (S n)) 
              m (Y : Ob C m) (f : Hom Y (Cft X)), Hom (star n X m Y f) X).

Definition Csystem_star_q := total2 (
   fun C : Csystem_ft_proj => Csystem_star_q_data C).

Definition Csystem_ft_proj_from_Csystem_star_q (C : Csystem_star_q) : Csystem_ft_proj :=
   pr1 C.
Coercion Csystem_ft_proj_from_Csystem_star_q : Csystem_star_q >-> Csystem_ft_proj.

Definition Cstar {C : Csystem_star_q}{n : nat} (X : Ob C (S n)) {m : nat}
    {Y : Ob C m} (f : Hom Y (Cft X)) : Ob C (S m) := pr1 (pr2 C) n X m Y f.

Definition Cq {C : Csystem_star_q}{n : nat} (X : Ob C (S n)) {m : nat}
    (Y : Ob C m) (f : Hom Y (Cft X)) : Hom (Cstar _ f) X := pr2 (pr2 C) n X m Y f.


(** ** Definition of being a pullback *)
(** Input: a square of arrows *)

Definition is_pullback (C : Csystem_catdata) {n m k l : nat}
   (a : Ob C n) (b : Ob C m) (c : Ob C k) (d : Ob C l) 
   (f : Hom a b) (g : Hom a c) (h : Hom b d) (i : Hom c d) :=
  dirprod (f ;; h == g ;; i) 
       (forall n' (a' : Ob C n') (f' : Hom a' b) (g' : Hom a' c),
         f' ;; h == g' ;; i ->
         
         exists_unique (fun fg' : Hom a' a => 
              hProppair (dirprod (fg' ;; f == f')(fg' ;; g == g')) 
              (isapropdirprod _ _ (isaset_Hom a' b _ _ )(isaset_Hom a' c _ _ ))
                )).




                  (isapropdirprod _ _ (isaset_Hom ) a'))). (isaset_Hom _ _ ) a )
)).
         
         total2 (fun fg' : Hom a' a =>
               dirprod (fg' ;; f == f')(fg' ;; g == g'))).


       True.




=> forall n (a : Ob C n) 
        (f : Mor a 

Definition final_in_Csystem_cat (C : Csystem_cat) := total2


Definition id_type (c : Csystem_predata) := forall n (a : Ob c n), Hom a a.

Definition comp_type (c : Csystem_predata) := forall n m k 
    (a : Ob c n) (b : Ob c m) (c : Ob c k),
    forall (f : Hom a b) (g : Hom b c), Hom a c.

Definition assoc (c : Csystem_predata)


    ob : nat -> hSet
    mor : nat -> nat -> hSet


(** * Definition of C-Systems [Csystem] *)
(** Definition is given in several steps:
   - [Csystem_predata] : a [catqalg] with length [Clength], 
                          point [Cpt] and father [Cft]
   - [Csystem_data] : predata + canonical projections + 
                        data which later forms pullbacks of can. projs.
*)


(** ** Csystem-predata *)

Definition Csystem_predata := total2 ( fun C : catqalg =>
  dirprod (catqalgobjects C -> nat)
          (dirprod (catqalgobjects C)
                   (catqalgobjects C -> catqalgobjects C))).

Definition catqalg_from_csystem_predata (C : Csystem_predata) : 
      catqalg := pr1 C.
Coercion catqalg_from_csystem_predata : Csystem_predata >-> catqalg.

Definition Clength {C : Csystem_predata} : C -> nat := pr1 (pr2 C).
Definition Cpt (C : Csystem_predata) : C := pr1 (pr2 (pr2 C)).
Definition Cft {C : Csystem_predata} : C -> C := pr2 (pr2 (pr2 C)).

(** ** Pullback-data : object + morphism starting in this object *)

Definition Csystem_pb_data (C : Csystem_predata) := total2 (
  fun fstar : forall X : C, Clength X > 0 ->
                forall Y : C, forall f : catqalghom Y (Cft X), C =>
    forall (X : C) (H : Clength X > 0) (Y : C)
           (f : catqalghom Y (Cft X)), 
       catqalghom (fstar X H Y f) X).

(** ** [Csystem_data] as described above *)

Definition Csystem_data := total2 (fun C : Csystem_predata =>
   dirprod (forall X : C, catqalghom X (Cft X)) 
           (Csystem_pb_data C)).

Definition Csystem_data_from_Csystem_predata (C : Csystem_data):
  Csystem_predata := pr1 C.
Coercion Csystem_data_from_Csystem_predata : 
   Csystem_data >-> Csystem_predata.

Definition Ccanprojection {C : Csystem_data}(X : C) : 
    catqalghom X (Cft X) := pr1 (pr2 C) X.

Definition Cprojpbobject {C : Csystem_data} X (H : Clength X > 0)
         {Y} (f : catqalghom Y (Cft X)) : C :=
   pr1 (pr2 (pr2 C)) X H Y f.

Definition Cq {C : Csystem_data} (X : C) (H : Clength X > 0)
      {Y} (f : catqalghom Y (Cft X)) : catqalghom (Cprojpbobject X H f) X :=
   pr2 (pr2 (pr2 C)) X H Y f.

(** ** Axioms of a C-System *)

(* for now we are missing the pullbacks  *)

Definition Csystem_axioms (C : Csystem_data) :=
 dirprod (
  dirprod (forall X : C, Clength X == 0 <-> X == Cpt C)
          (forall X : C, Clength X > 0 ->
              Clength (Cft X) == (Clength X - 1)%nat)
         )
         (
  dirprod (Cft (Cpt C) == Cpt C)
          (isfinal_in_catqalg C (Cpt C))
         ).


(** ** below are only notes *)
(*
Record cstructure := {
 
  ob : nat -> hSet 
     where "'Ob'" := (tpair isaset (total2 ob) 
           (sigset ob isasetnat 
             (fun n : nat => pr2 (ob n)))) ;
  mor : hSet ;
  s : mor -> total2 ob ;
  t : mor -> total2 ob ;
  comp : hfp s t -> mor ; 
  id : total2 ob -> mor ;
  categorical : category Ob mor s t comp id ;
  pt : ob 0 ;
  ft : forall {n : nat}, ob (S n) -> ob n ;
  canonical : forall n (X : ob (S n)),
      Hom Ob _ s t  (tpair _ (S n) X) (tpair _ n (ft X)) ;

       (* mor ; (* refine towards HomSets*) *)
  can_pb : forall {n : nat} (X : ob (S n)) {m : nat}
       (Y : ob m) (f : mor) 
       (HfY : s f == tpair _ m Y) 
       (HfX : t f == tpair _ n (ft X)),
        ob (S m) ;
  can_pb_map : forall {n : nat} (X : ob (S n)) {m : nat}
       (Y : ob m) (f : mor) 
       (HfY : s f == tpair _ m Y) 
       (HfX : t f == tpair _ n (ft X)),
       mor ;
  can_pb_s : forall {n : nat} (X : ob (S n)) {m : nat}
       (Y : ob m) (f : mor) 
       (HfY : s f == tpair _ m Y) 
       (HfX : t f == tpair _ n (ft X)),
       s (can_pb_map X Y f HfY HfX) == 
           tpair _ (S m) (can_pb X Y f HfY HfX) ;
  can_pb_t : forall {n : nat} (X : ob (S n)) {m : nat}
       (Y : ob m) (f : mor) 
       (HfY : s f == tpair _ m Y) 
       (HfX : t f == tpair _ n (ft X)),
        t (can_pb_map X Y f HfY HfX) == 
           tpair _ (S n) X ;
  
  ob0pt : forall X : ob 0, X == pt ;
   
  pt_final : final_obj Ob mor s t (tpair _ 0 pt) ;

  can_pb_ft : forall {n : nat} (X : ob (S n)) {m : nat}
       (Y : ob m) (f : mor) 
       (HfY : s f == tpair _ m Y) 
       (HfX : t f == tpair _ n (ft X)),
        (tpair _ m (ft (can_pb X Y f HfY HfX)) == 
        (tpair _ m Y)) ;

  pb_condition : forall (n : nat)(X : ob (S n)) 
                m {Y : ob m}
                  (f : Hom Ob mor s t 
                (tpair _ m Y)
                (tpair _ n (ft X)) 
                ),
      is_pullback Ob _ s t comp f 
         (canonical _ X) (can_pb_map X Y f (pr1 (pr2 f)) (pr2 (pr2 f)) )
         (canonical _ (can_pb X Y f (pr1 (pr2 f)) (pr2 (pr2 f)) )) ;
         
  can_pb_id : forall n (X : ob (S n)), 
           can_pb X (ft X) (id (tpair _ n (ft X)))
             (id_s Ob mor s t comp id categorical _ )

         (id_t Ob mor s t comp id categorical _ )
           == X ;
  
  can_pb_map_id : forall n (X : ob (S n)), 
           can_pb_map X (ft X) (id (tpair _ n (ft X)))
             (id_s Ob mor s t comp id categorical _ )

         (id_t Ob mor s t comp id categorical _ )
           == id (tpair _ (S n) X) ;

  
  can_pb_comp : forall n (X : ob (S n)), 
            forall m (Y : ob m), forall k (Z : ob k),
           forall (f : mor)
         (Hsf : s f == (tpair _ m Y))
         (Htf : t f == (tpair _ n (ft X))),
           forall (g : mor)
         (Hsg : s g == (tpair _ k Z))
         (Htg : t g == (tpair _ m Y)),
    can_pb X Z (comp (hfp_pair s t f g (Htg @ !Hsf) )) 
       (comp_s Ob mor s t comp id categorical g f (Htg @ !Hsf) @ Hsg)
       (comp_t Ob mor s t comp id categorical g f (Htg @ !Hsf) @ Htf )  == 
        can_pb (can_pb X Y f Hsf Htf) Z g Hsg 
          (Htg @ !can_pb_ft X Y f Hsf Htf)
  ;       
  
  can_pb_map_comp : 
        forall n (X : ob (S n)), 
            forall m (Y : ob m), forall k (Z : ob k),
           forall (f : mor)
         (Hsf : s f == (tpair _ m Y))
         (Htf : t f == (tpair _ n (ft X))),
           forall (g : mor)
         (Hsg : s g == (tpair _ k Z))
         (Htg : t g == (tpair _ m Y)),
      
     can_pb_map X _ (comp (hfp_pair s t f g (Htg @ !Hsf) ))  
       (comp_s Ob mor s t comp id categorical g f (Htg @ !Hsf) @ Hsg)
       (comp_t Ob mor s t comp id categorical g f (Htg @ !Hsf) @ Htf)
== 
    comp 
      (hfp_pair s t 
        (can_pb_map X Y f Hsf Htf )
        (can_pb_map (can_pb X Y f Hsf Htf ) Z g Hsg 
            (Htg @  !can_pb_ft _ _ _ _ _  ))
       (can_pb_t _ _ _ _ _ @ !can_pb_s X Y f Hsf Htf ) )
     
}.


Check (fun X : cstructure => ob X).
*)