(* Contribution to the Coq Library   V6.3 (July 1999)                    *)
(*     A development written by Pierre Castéran for Coq V6.1
     
Coq : A product of inria : "http://pauillac.inria.fr/coq/coq-eng.html"

Pierre Castéran : A product of LaBRI : 


LaBRI, Universite Bordeaux-I      |    12 place Puy Paulin
351 Cours de la Liberation        |    33000 Bordeaux
F-33405 TALENCE Cedex             |    France
France                            |    (+ 33) 5 56 81 15 80
tel : (+ 33) 5 56 84 69 31
fax : (+ 33) 5 56 84 66 69
email: casteran@labri.u-bordeaux.fr       
www: http://dept-info.labri.u-bordeaux.fr/~casteran

"Les rêves sont aussi beaux que la réalité, mais ils ne sont pas mieux".
( J.L.Borges )

*)



(* VI    Deletion.
******************
*******************


  Deleting an element from a binary search tree is a little more
  complex than inserting or searching.
  The difficult case is the deletion of the root of a tree; we have
  to reconstruct a search tree. To solve this problem, we define
  an auxiliary operation: deleting the greatest element of a non-empty
  binary search tree.
*)

(* VI.2  Deletion in general
****************************

  We are now ready to study the remove operation in it's generality:
 (RM n t t') if t' is a search tree obtained by removing n from t *)

Require Import nat_trees.
Require Import search_trees.
Require Import DeleteMax.
Require Import Arith.
Require Import Compare_dec.


Inductive RM (n : nat) (t t' : nat_tree) : Prop :=
    rm_intro :
      ~ occ t' n ->
      (forall p : nat, occ t' p -> occ t p) ->
      (forall p : nat, occ t p -> occ t' p \/ n = p) ->
      search t' -> RM n t t'.

Hint Resolve rm_intro: searchtrees.


(* base cases *)

Remark RM_0 : forall n : nat, RM n NIL NIL.
(*********************************)
Proof.
intro n; apply rm_intro; auto with searchtrees v62.
Qed.

Hint Resolve RM_0: searchtrees.


Remark RM_1 : forall n : nat, RM n (bin n NIL NIL) NIL.
(*********************************************)
Proof.
intros; apply rm_intro; auto with searchtrees v62.
intros p H; elim (occ_inv n _ _ _ H); auto with searchtrees v62.
tauto.
Qed.

Hint Resolve RM_1: searchtrees.


(* deleting in the left son *)

Remark rm_left :
 forall (n p : nat) (t1 t2 t' : nat_tree),
 p < n ->
 search (bin n t1 t2) -> RM p t1 t' -> RM p (bin n t1 t2) (bin n t' t2).
(*************************************************)
Proof.
intros n p t1 t2 t' H H0 H1.
apply rm_intro. unfold not in |- *; intro H2.
elim (occ_inv n p t' t2).
intro eg; absurd (p < p); auto with searchtrees v62.
pattern p at 2 in |- *; elim eg; auto with searchtrees v62.
intro D; elim D; intro H3. 
elim H1; auto with searchtrees v62.
absurd (occ t2 p); auto with searchtrees v62.
apply not_right with n t1; auto with searchtrees v62.
auto with searchtrees v62.
intros p0 H2.
elim (occ_inv n p0 t' t2).
simple induction 1; auto with searchtrees v62.
simple induction 1; auto with searchtrees v62.
intro; elim H1; auto with searchtrees v62.
auto with searchtrees v62.
intros.
elim (occ_inv n p0 t1 t2).
simple induction 1; auto with searchtrees v62.
simple induction 1; intro H4.
elim H1.
intros H5 H6 H7 H8.
elim (H7 p0 H4); auto with searchtrees v62.
auto with searchtrees v62.
auto with searchtrees v62.
apply bin_search.
elim H1; auto with searchtrees v62.
apply search_r with n t1; auto with searchtrees v62.
apply maj_intro; intros q H2.
cut (occ t1 q).
intro; elim (maj_l n t1 t2 H0); intros; auto with searchtrees v62.
auto with searchtrees v62.
elim H1; auto with searchtrees v62.
apply min_r with t1; auto with searchtrees v62.
Qed.

Hint Resolve rm_left: searchtrees.


(* deleting in the right son *)

Remark rm_right :
 forall (n p : nat) (t1 t2 t' : nat_tree),
 n < p ->
 search (bin n t1 t2) -> RM p t2 t' -> RM p (bin n t1 t2) (bin n t1 t').
(**************************************************)
Proof.
intros n p t1 t2 t' H H0 H1.
apply rm_intro.
unfold not in |- *; intro H2.
elim (occ_inv n p t1 t').
intro eg; absurd (p < p); auto with searchtrees v62.
pattern p at 1 in |- *; elim eg; auto with searchtrees v62.
intro D; elim D; intro H3. 
elim H1; auto with searchtrees v62.
absurd (occ t1 p).
apply not_left with n t2; auto with searchtrees v62.
auto with searchtrees v62.
elim H1; auto with searchtrees v62.
auto with searchtrees v62.
intros p0 H2.
elim (occ_inv n p0 t1 t').
simple induction 1; auto with searchtrees v62.
simple induction 1; auto with searchtrees v62.
intro; elim H1; auto with searchtrees v62.
auto with searchtrees v62.
intros.
elim (occ_inv n p0 t1 t2).
simple induction 1; auto with searchtrees v62.
simple induction 1; auto with searchtrees v62.
intro H4.
elim H1; intros H5 H6 H7 H8.
elim (H7 p0 H4); auto with searchtrees v62.
auto with searchtrees v62.
apply bin_search.
apply search_l with n t2; auto with searchtrees v62.
elim H1; auto with searchtrees v62.
apply maj_l with t2; auto with searchtrees v62.
apply min_intro; intros q H2.
cut (occ t2 q).
intro.
elim (min_r n t1 t2 H0); auto with searchtrees v62. 
elim H1; auto with searchtrees v62.
Qed.

Hint Resolve rm_right: searchtrees.


(* base case for deleting the root *)

Remark rm_NILt :
 forall (n : nat) (t : nat_tree),
 search (bin n NIL t) -> RM n (bin n NIL t) t.
(*******************************************************)
Proof.
intros; apply rm_intro.
apply not_right with n NIL; auto with searchtrees v62.
auto with searchtrees v62.
intros p H1; elim (occ_inv n p NIL t H1); intro H2.
right; auto with searchtrees v62.
elim H2; intro.
absurd (occ NIL p); auto with searchtrees v62.
left; auto with searchtrees v62.
apply search_r with n NIL; auto with searchtrees v62.
Qed.

Hint Resolve rm_NILt: searchtrees.


(* General case: we use the RMAX predicate *)

Section rm_root.
     Variable n p : nat.
     Variable t1 t2 t' : nat_tree.
     Hypothesis S : search (bin n (bin p t1 t2) t').
     Variable q : nat.
     Variable t0 : nat_tree.
     Hypothesis R : RMAX (bin p t1 t2) t0 q.
     Hint Resolve S: searchtrees.
     
     Remark rm_2 : q < n.
     (********************)
     Proof.
     elim R.
     intros.
     elim (maj_l n (bin p t1 t2) t').
     auto with searchtrees v62.
     auto with searchtrees v62.
     Qed.

     Hint Resolve rm_2: searchtrees.
     
     Remark rm_3 : ~ occ (bin q t0 t') n.
     (**********************************)
     Proof.
     unfold not in |- *; intro H.
     elim (occ_inv q n t0 t').
     intro eg; absurd (q < q); auto with searchtrees v62.
     pattern q at 2 in |- *; rewrite eg; auto with searchtrees v62.
     intro D; elim D; intro H'.
     elim R; intros H0 H1 H2 H3 H4 H5.
     absurd (occ (bin p t1 t2) n); auto with searchtrees v62.
     apply not_left with n t'; auto with searchtrees v62.
     absurd (occ t' n); auto with searchtrees v62.
     apply not_right with n (bin p t1 t2); auto with searchtrees v62.
     auto with searchtrees v62.
     Qed.

     Hint Resolve rm_3: searchtrees.
     

     Remark rm_4 :
      forall p0 : nat,
      occ (bin q t0 t') p0 -> occ (bin n (bin p t1 t2) t') p0.
     (***************************************************************)
     Proof. 
     intros p0 H.
     elim (occ_inv q p0 t0 t' H).  
     intro eg.
     elim R; rewrite eg; auto with searchtrees v62.
     simple induction 1; auto with searchtrees v62.
     intro H'. elim R; auto with searchtrees v62.
     Qed.

     Hint Resolve rm_4: searchtrees.
     

     Remark rm_5 :
      forall p0 : nat,
      occ (bin n (bin p t1 t2) t') p0 -> occ (bin q t0 t') p0 \/ n = p0.
     (********************************************)
     Proof.
     intros p0 H.
     elim (occ_inv n p0 (bin p t1 t2) t'). 
     simple induction 1; auto with searchtrees v62.
     simple induction 1.
     intro H1.
     elim R; intros H2 H3 H4 H5 H6 H7.
     elim (H5 p0 H1). intro; left; auto with searchtrees v62.
     simple induction 1; left; auto with searchtrees v62.
     intro; left; auto with searchtrees v62.
     auto with searchtrees v62.
     Qed.

     Hint Resolve rm_5: searchtrees.
     

     Remark rm_6 : search (bin q t0 t').
     (**********************************)
     Proof.
     apply bin_search.
     elim R; auto with searchtrees v62.
     apply search_r with n (bin p t1 t2); auto with searchtrees v62.
     elim R; intros H H0 H1 H2 H3 H4.
     apply maj_intro.
     intros q0 H5; elim (le_lt_or_eq q0 q (H0 q0 (H1 q0 H5))).
     auto with searchtrees v62.
     intro eg; absurd (occ t0 q0).
     rewrite eg; auto with searchtrees v62.
     auto with searchtrees v62.
     apply min_intro.
     intros q0 H. 
     apply lt_trans with n. 
     elim R; auto with searchtrees v62.
     elim (min_r n (bin p t1 t2) t'). 
     auto with searchtrees v62. 
     auto with searchtrees v62.
     Qed.

     Hint Resolve rm_6: searchtrees.
     

     Lemma rm_root_lemma : RM n (bin n (bin p t1 t2) t') (bin q t0 t').
     (********************************************************************)
     Proof.
     apply rm_intro; auto with searchtrees v62.
     Qed.
     
End rm_root.


(* The final algorithm *)

Theorem rm :
 forall (n : nat) (t : nat_tree), search t -> {t' : nat_tree | RM n t t'}.
(*********************************************)
Proof.
 simple induction t;
  [ intros s; exists NIL
  | intros p; elim (le_gt_dec n p); intros h;
     [ elim (le_lt_eq_dec n p h); intros h';
        [ intros t1 hr1 t2 hr2 s; elim hr1;
           [ intros t3 h3; exists (bin p t3 t2) | idtac ]
        | intros t1; case t1;
           [ intros hr1 t2 hr2 s; exists t2
           | intros p' t1' t2' hr1 t2 hr2 s; elim (rmax (bin p' t1' t2'));
              [ intros q ex; elim ex; intros t' H; exists (bin q t' t2)
              | idtac
              | idtac ] ] ]
     | intros t1 hr1 t2 hr2 s; elim hr2;
        [ intros t3 h3; exists (bin p t1 t3) | idtac ] ] ];
  auto with searchtrees v62.

(* 
 Realizer Fix rm{rm/2 : nat -> nat_tree -> nat_tree :=
       [n:nat][t:nat_tree]
          <nat_tree> Cases t of
                NIL => NIL
              | (bin p t1 t2) =>
                 <nat_tree> if (le_gt_dec n p)
			    then <nat_tree> if (le_lt_eq_dec n p)
				 then (bin p (rm n t1) t2)
				 else (<nat_tree> Cases t1 of
                                        NIL => t2
                                      | _   => 
                                       <nat_tree>let (q,t')=  (rmax  t1)
                                                 in (bin q t' t2)
                                      end)
                            else (bin p t1 (rm n t2)) 
           end }.

 Program_all.
*)
 eapply search_l; eauto with searchtrees v62.
 rewrite h'; apply rm_NILt; auto with searchtrees v62.
 rewrite h'; apply rm_root_lemma; auto with searchtrees v62.
 eapply search_l; eauto with searchtrees v62.
 eapply search_r; eauto with searchtrees v62.
 
Qed.




