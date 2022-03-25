(* (c) Copyright 2006-2018 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From fourcolor Require Import color ctree dyck.

(******************************************************************************)
(*   Creation of an initial (full) coloring tree and its correctness theorem. *)
(* This tree is constructed using dynamic programming, tabulating first its   *)
(* leaves, then subtrees of height 1, 2, etc, until h - 2, where h is the     *)
(* perimeter length / ring size. Subtrees of odd traces are pruned at this    *)
(* stage, and the final tree (of height h - 1) is assembled from the three    *)
(* pruned subtrees of height h - 2.                                           *)
(*   The tables are simply lists of tree pairs. The i'th pair consists of the *)
(* two subtrees that can occur after a trace where Color2 and Color3 occur a  *)
(* total of i times; the first component of the pair occurs at traces t whose *)
(* color sum is even (~~ color_bit0 (sumt t)), the second at odd-sum traces.  *)
(*   Main definitions:                                                        *)
(* ctree_init_tree h == the full tree storing all even partial traces for     *)
(*                  ring size h.                                              *)
(*   ctree_table := seq ctree_pair, the type of tables storing subtrees of a  *)
(*                  given height of the full tree for a given ring size.      *)
(*  ctree_table_sub tab i b == the ctree in tab : ctree_table storing traces  *)
(*                  that can occur after a trace et where Color2 and Color3   *)
(*                  occur a total of i times and whose color sum has parity b *)
(*                  (color_bit0 (sumt et) == b).                              *)
(* ctree_leaf_table h == the table of non empty leaves at ring size h.        *)
(* ctree_merge_table tab == compute the table of subtrees of height n+1 from  *)
(*                  the table of subtrees of height n.                        *)
(* ctree_prune_i t == prune all branches of t where Color i+2 occurs before   *)
(*                 Color i+1 (with i in [1,3], and +1 cycling from 3 to 1).   *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition ctree_table := seq ctree_pair.

Section InitCtree.

Notation ctz := ctree_empty_pair (only parsing).

Definition ctree_table_sub (tab : ctree_table) n23 :=
  ctree_pair_sub (nth ctz tab n23).

(* First, leaf construction.                                                 *)

Fixpoint ctree_add_dyck m n :=
  if n is n'.+1 then iteri m.+1 (fun m' => ctree_add_dyck m'.+1 n') else
  CtreeLeaf.

Fixpoint ctree_leaf_table_from lf n h : ctree_table :=
  match h with
  | 0 => [::]
  | 1 => [:: CtreePair lf lf]
  | h'.+2 =>
      [:: CtreePair lf lf, CtreePair CtreeEmpty lf
        & ctree_leaf_table_from (ctree_add_dyck 2 n lf) n.+1 h']
  end.

Definition ctree_leaf_table h : ctree_table :=
  let leaf1 := CtreeLeaf CtreeEmpty in
  CtreePair CtreeEmpty leaf1 :: ctree_leaf_table_from leaf1 0 h.

(* Pairs are merged pairwise to build higher trees.                          *)
(* CtreeNode instead of ctree_cons would be correct here, but hard to prove. *)

Definition ctree_merge_pair tu tu' :=
  let: CtreePair t0 t1 := tu in let: CtreePair t2 t3 := tu' in
  CtreePair (ctree_cons t1 t2 t3) (ctree_cons t0 t3 t2).

Definition ctree_merge_table (tab : ctree_table) : ctree_table :=
  if tab is line :: tab' then pairmap ctree_merge_pair line tab' else tab.

(* Pruning odd permutations.                                                 *)

Fixpoint ctree_prune_1 t :=
  if t is CtreeNode t1 t2 t3 then
    ctree_cons (ctree_prune_1 t1) t2 CtreeEmpty
  else t.

Fixpoint ctree_prune_2 t :=
  if t is CtreeNode t1 t2 t3 then
    ctree_cons CtreeEmpty (ctree_prune_2 t2) t3
  else t.

Fixpoint ctree_prune_3 t :=
  if t is CtreeNode t1 t2 t3 then
    ctree_cons t1 CtreeEmpty (ctree_prune_3 t3)
  else t.

(* Putting everything together.                                              *)

Definition ctree_init_tree h :=
  if iter h.-1 ctree_merge_table (ctree_leaf_table h)
    is [:: CtreePair t0 t1, CtreePair t2 t3 & _]
  then ctree_cons (ctree_prune_1 t1) (ctree_prune_2 t2) (ctree_prune_3 t3)
  else CtreeEmpty.

(* Leaf correctness. *)

Lemma ctree_add_dyck_leaf_of m n d :
  ctree_add_dyck m n (ctree_leaf_of d)
   = ctree_leaf_of (gen_dyck m.+1 (m + n.*2) + d).
Proof.
elim: n m d => [|n IHn] m /=; first by rewrite addn0 gen_dyck_all_close.
elim: m => [|m IHm] d; rewrite doubleS /=; first by rewrite addn0 IHn.
by rewrite IHm IHn doubleS addnA -addnE !addnS.
Qed.

Lemma ctree_leaf_table_size h : size (ctree_leaf_table h) = h.+1.
Proof.
rewrite /ctree_leaf_table_from /=; congr _.+1.
rewrite -(odd_double_half h) addnC; move: (CtreeLeaf CtreeEmpty) 0.
by elim: h./2 => [|h2 IHh] t n; [case: (odd h) | rewrite /= IHh].
Qed.

Lemma ctree_leaf_table_sub h i b0 :
   i <= h ->
   let cet := [:: ccons (odd i) b0] in let n_i := i + count_cbit1 cet in
  ctree_table_sub (ctree_leaf_table h) i b0
   = (if Color0 \in cet then CtreeEmpty else ctree_leaf_of (dyck n_i)).
Proof.
rewrite /ctree_leaf_table -{1 2 4}[i]odd_double_half.
move: (odd i) i./2 => b1 m; rewrite (addnC b1) => lemh.
rewrite /= cbit1_ccons inE addn0 -addnA -{2}[m]addn0.
set t1 := CtreeLeaf _; rewrite -{1}[t1]/(ctree_leaf_of (dyck 0.*2)).
rewrite -{t1}[t1]/(ctree_leaf_of (dyck 1.*2)).
elim: m 0 h lemh => [|m IHm] n.
  by rewrite /= !add0n addnC; case: b1 b0 => [[] [|[]] | []].
case=> [|[|h]] // /(IHm n.+1); rewrite addSnnS => <-.
by rewrite /dyck /= ctree_add_dyck_leaf_of !addn0.
Qed.

(* Global correctness; we run through the construction twice, once to check *)
(* that subtrees are proper, and once to check the counts.                  *)

Lemma ctree_init_tree_proper h : ctree_proper h (ctree_init_tree h).
Proof.
case Dh: h => [|h'] //=; rewrite /ctree_init_tree.
move Dltab: (ctree_leaf_table _) => ltab /=; move Dtab: (iter _ _ ltab) => tab.
have{Dtab ltab Dltab} [Dsz sub_ok]: h' + size tab = h.+1
  /\ forall i b0, i < size tab -> ctree_proper h' (ctree_table_sub tab i b0).
- have:= leqnSn h'; rewrite -{tab}Dtab -Dh.
  elim: (h') => [_ | n IHn /leqW ltnh].
    rewrite /= -{ltab}Dltab -Dh ctree_leaf_table_size; split=> // i b0 leih.
    rewrite ctree_leaf_table_sub //; case: ifP => // _.
    exact: ctree_leaf_of_proper.
  move Dctp': (ctree_proper n.+1) => ctp' /=.
  case: (iter n _ ltab) {IHn}(IHn ltnh) => [|pt0 tab] [Dn tab_ok].
    by rewrite -Dn /= addn0 ltnn in ltnh.
  rewrite /= addSnnS size_pairmap /=; split=> {Dn}// i b0 ltitab.
  move/tab_ok: (ltnW ltitab); move/(tab_ok i.+1): (ltitab) => {tab_ok}.
  rewrite /ctree_table_sub (nth_pairmap ctz) {ltitab}//=.
  case: (nth _ _ i) => t0 t1; case: {i tab}(nth _ _ i) => t2 t3.
  do 2![move=> t_ok; move: {t_ok}(t_ok false) (t_ok true) => /= ? ?].
  by case: b0; rewrite /= -Dctp'; apply ctree_cons_proper.
have{h Dh}{} Dsz: size tab = 2 by apply: (@addnI h'); rewrite Dsz Dh addn2.
case: tab Dsz => [|[t0 t1] [|[t2 t3] tab']] //= _ in sub_ok *.
have ok1 := sub_ok 1 _ isT.
move: {sub_ok ok1}(sub_ok 0 true isT) (ok1 false) (ok1 true).
rewrite /ctree_table_sub {t0 tab'}/= => t1ok t2ok t3ok.
apply ctree_cons_proper;
 [ move: t1 t1ok {t2 t2ok t3 t3ok}
 | move: {t1 t1ok} t2 t2ok {t3 t3ok}
 | move: {t1 t1ok t2 t2ok} t3 t3ok ];
 elim: h' => [|h IHh] [t1 t2 t3|lf|] //= [_ t1ok t2ok t3ok];
 by apply ctree_cons_proper => //; apply: IHh.
Qed.

Lemma ctree_sub_init_tree h (et : colseq) :
 let et_ok := [&& size et == h, Color0 \notin ctrace et & even_trace et] in
 ctree_sub (ctree_init_tree h) et = 
   (if et_ok then dyck (count_cbit1 (ctrace et)) else 0).
Proof.
case Dh: h => [|h']; [by case: et | rewrite /ctree_init_tree [_.-1]/= -Dh].
move Dltab: (ctree_leaf_table h) => ltab; move Dtab: (iter _ _ ltab) => tab.
have{ltab Dtab Dltab} [Dsz Dsub]: h' + size tab = h.+1
    /\ forall i, i < size tab -> forall b0 et,
       let cet := rcons et (ccons (odd i) b0 +c sumt et) in
       let et_ok := (size et == h') && (Color0 \notin cet) in
       ctree_sub (ctree_table_sub tab i b0) et
         = (if et_ok then dyck (i + count_cbit1 cet) else 0).
- have:= leqnSn h'; rewrite -{et tab}Dtab -Dh.
  elim: (h') => [_ | n IHn /leqW ltnh] /=.
    rewrite -{ltab}Dltab ctree_leaf_table_size add0n; split=> //= i ileh b0.
    rewrite ctree_leaf_table_sub //; move: (ccons _ _) => c.
    by case=> *; rewrite ?addc0; case: ifP => // _; apply: ctree_sub_leaf_of.
  case: (iter n _ _) {IHn}(IHn ltnh) => [|pt tab] [Dn tab_ok].
    by rewrite -Dn /= addn0 ltnn in ltnh.
  rewrite /= size_pairmap addSnnS {}Dn; split=> // i ltitab b0.
  move: {tab_ok}(tab_ok i (ltnW ltitab)) (tab_ok i.+1 ltitab).
  rewrite /ctree_table_sub (nth_pairmap ctz) {ltitab}//=.
  case: {pt}(nth _ _ i) => t0 t1; case: {tab}(nth _ _ i) => t2 t3.
  do 2![move=> Dsub; move: {Dsub}(Dsub false) (Dsub true) => /= ? ?].
  case=> [|e et]; first by case: b0; rewrite ctree_sub_cons.
  rewrite /= addcA eqSS -[_ +c e]ccons_cbits inE.
  rewrite cbit0_addc cbit0_ccons cbit1_addc cbit1_ccons.
  case: e; rewrite /= ?addbT ?addbF -1?addSnnS;
    by case: b0; rewrite /= ctree_sub_cons /= ?andbF ?add0n.
have {}Dsz: size tab = 2 by apply: (@addnI h'); rewrite Dsz Dh addnC.
case: tab Dsz => [|[t0 t1] [|[t2 t3] tab']] //= _ in Dsub *.
move Dtec: {-}(even_trace et) => tec; rewrite /= ctree_sub_cons {h}Dh.
case: et => [|e et] //= in Dtec *; rewrite eqSS.
move: {Dsub}(Dsub 0 isT true et) (Dsub 1 isT false et) (Dsub 1 isT true et).
rewrite /ctree_table_sub {t0 tab'}/= => Dt1 Dt2 Dt3.
case: e Dtec; [by rewrite andbF | move: t1 Dt1 | move: t2 Dt2 | move: t3 Dt3];
  by clear=> t Dt Dtec; transitivity (if tec then ctree_sub t et else 0);
  [ rewrite -{h' tec Dt}Dtec; elim: et t => [|e et IHet] [t1 t2 t3|lf|];
    rewrite /= ?if_same // ctree_sub_cons //; case: e; rewrite /= ?if_same
  | by rewrite Dtec andbA andbC; case tec].
Qed.

End InitCtree.
