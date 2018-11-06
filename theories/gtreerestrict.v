(* (c) Copyright 2006-2018 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrfun ssrbool eqtype ssrnat seq.
From fourcolor
Require Import color ctree chromogram gtree.

(******************************************************************************)
(* This is the first phase of a D-reducibility step: removing from the set of *)
(* (partial) chromograms set those that match a set of admissible colorings.  *)
(* The result of this step is a partition of the set into deleted and         *)
(* remaining chromograms, represented by a gtree_pair. To save overhead we    *)
(* do a single pass over the gtree, passing down a list of matching ctree's   *)
(* to delete. In the proof this list has size at most 32, and usually size at *)
(* most 8.                                                                    *)
(* Main definitions:                                                          *)
(*  gtree_restriction == a monomorphic type representing a set of trace       *)
(*                    matches to be removed from a gtree. It is equivalent to *)
(*                    seq (bit_stack * ctree), with each pair (bs, ct) in the *)
(*                    sequence standing for the 'matches' (bs, et, w) such    *)
(*                    matchpg bs et w, and ctree_mem ct et.                   *)
(*  gtr_cons bs ct gtr == adds the pair (bs, ct) to gtr : gtree_restriction.  *)
(*  gtr_mem gtr w <=> the gtree_restriction gtr contains a match (bs, et, w)  *)
(*                    with the partial chromogram w.                          *)
(*                    the set repesented by ctr : ctree_restriction.          *)
(* gtr_split k r0 r1 r2 r3 gtr == continuation-passing style split of gtr;    *)
(*                    adds to each gtree_restriction r_i the (bs, ct) pairs   *)
(*                    repesenting matches (bs, et, w) that correspond 1-to-1  *)
(*                    to matches (bs', e :: et, s_i :: w) in gtr, where s_i   *)
(*                    is the ith gram_symbol in [Gskip, Gpush, Gpop0, Gpop1], *)
(*                    then calls k on the resulting 4-tuple. With gtr_split   *)
(*                    we can view and eliminate a gtree_restriction as a      *)
(*                    gtree - both denote sets of chromogram.                 *)
(* gtree_restrict gt gtr == a gtree_pair partition pt of gt : gtree, whose    *)
(*                    first component is obtained by removing all matches in  *)
(*                    gtr : ctree_restriction from those in gt.               *)
(* gtr_match[0123] gtr <=> the matches represented by gtr contain the size 1  *)
(*                    chromogram [s_i], where s_i is the ith gram_symbol, and *)
(*                    i is [0123], respectively.                              *)
(*  gtp_e_01, etc. == a statically defined gtree_pair of GtreeEmpty and       *)
(*                    GtreeLeaf01 (there 24 variation in all, e.g., gtp_0_e). *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section GtreeRestrict.

Inductive gtree_restriction :=
  GtrNil | GtrCons of bit_stack & ctree & gtree_restriction.

(* A restriction set represents a set of matching chromograms *)

Fixpoint gtr_mem r w :=
  if r isn't GtrCons bs t r' then false else
  has_match bs (ctree_mem t) w || gtr_mem r' w.

Definition gtr_cons bs t r := if ctree_empty t then r else GtrCons bs t r.

Lemma gtr_mem_cons bs t r w :
 gtr_mem (gtr_cons bs t r) w = has_match bs (ctree_mem t) w || gtr_mem r w.
Proof.
rewrite /gtr_cons; case: ifP => // /ctree_empty_eq-> /=; rewrite orb_idl //.
by case/has_matchP; case.
Qed.

Section GtrSplit.

Variables (A : Set) (continue : forall r0 r1 r2 r3 : gtree_restriction, A).

Fixpoint gtr_split r0 r1 r2 r3 r :=
  match r with
  | GtrNil => continue r0 r1 r2 r3
  | GtrCons bs (CtreeNode t1 t2 t3) r' =>
      let r02 := GtrCons (Bpush0 bs) t2 r0 in
      let r03 := GtrCons (Bpush1 bs) t3 r0 in
      let r023 := GtrCons (Bpush0 bs) t2 r03 in
      let r1' := if t1 is CtreeEmpty then r1 else GtrCons bs t1 r1 in
      let r2' bs' t':= GtrCons bs' t' r2 in
      let r3' bs' t' := GtrCons bs' t' r3 in
      match t2, t3, bs with
      | CtreeEmpty, CtreeEmpty, _ => gtr_split r0 r1' r2 r3 r'
      | CtreeEmpty, _, Bstack0 => gtr_split r03 r1' r2 r3 r'
      | CtreeEmpty, _, Bpush0 bs' => gtr_split r03 r1' r2 (r3' bs' t3) r'
      | CtreeEmpty, _, Bpush1 bs' => gtr_split r03 r1' (r2' bs' t3) r3 r'
      | _, CtreeEmpty, Bstack0 => gtr_split r02 r1' r2 r3 r'
      | _, CtreeEmpty, Bpush0 bs' => gtr_split r02 r1' (r2' bs' t2) r3 r'
      | _, CtreeEmpty, Bpush1 bs' => gtr_split r02 r1' r2 (r3' bs' t2) r'
      | _, _, Bstack0 => gtr_split r023 r1' r2 r3 r'
      | _, _, Bpush0 bs' => gtr_split r023 r1' (r2' bs' t2) (r3' bs' t3) r'
      | _, _, Bpush1 bs' => gtr_split r023 r1' (r2' bs' t3) (r3' bs' t2) r'
      end
  | GtrCons _ _ r' => gtr_split r0 r1 r2 r3 r'
  end.

Lemma gtr_split_some bs t1 t2 t3 r0 r1 r2 r3 r :
 let cons_pop t t' r' := match bs with
   | Bstack0 => r'
   | Bpush0 bs' => gtr_cons bs' t r'
   | Bpush1 bs' => gtr_cons bs' t' r'
   end in
 gtr_split r0 r1 r2 r3 (GtrCons bs (CtreeNode t1 t2 t3) r) =
 gtr_split (gtr_cons (Bpush0 bs) t2 (gtr_cons (Bpush1 bs) t3 r0))
           (gtr_cons bs t1 r1) (cons_pop t2 t3 r2) (cons_pop t3 t2 r3) r.
Proof.
by case: bs => [|bs|bs] /=; rewrite !fold_ctree_empty /gtr_cons; do 2!case: ifP.
Qed.

End GtrSplit.

Let gsplit r s :=
  let gtk gt0 gt1 gt2 gt3 := @gram_symbol_rec (fun _ => _) gt0 gt1 gt2 gt3 s in
  gtr_split gtk GtrNil GtrNil GtrNil GtrNil r.

Lemma gtr_split_eq A rk r :
 @gtr_split A rk GtrNil GtrNil GtrNil GtrNil r =
   rk (gsplit r Gpush) (gsplit r Gskip) (gsplit r Gpop0) (gsplit r Gpop1).
Proof.
rewrite /gsplit; move: GtrNil => rn.
move: rn {2 4 6 8 10}rn {3 6 9 12 15}rn {4 8 12 16 20}rn.
by elim: r => // bs [t1 t2 t3|lf|] r IHr *; rewrite ?gtr_split_some -IHr.
Qed.

Lemma gtr_mem_gsplit r s w : gtr_mem r (s :: w) = gtr_mem (gsplit r s) w.
Proof.
rewrite /gsplit; move Drn: GtrNil => rn; rewrite -[lhs in lhs = _]orFb.
have <-: gtr_mem (@gram_symbol_rec (fun _ => _) rn rn rn rn s) w = false.
  by rewrite -Drn; case: s.
elim: r rn {2 4}rn {3 6}rn {4 8}rn {Drn}; first by move=> *; rewrite /= orbF.
move=> bs [t1 t2 t3|lf|] r IHr r0 r1 r2 r3; rewrite ?gtr_split_some -?{}IHr;
  try by rewrite [s :: w]lock /= -lock; case: has_matchP => [[[]] | ].
case: s; rewrite /= ?gtr_mem_cons orbA {-2 3}[orb]lock orbC -?orbA -!lock //;
  by case: bs => *; rewrite ?gtr_mem_cons.
Qed.

Fixpoint gtr_match0 r :=
  match r with
  | GtrNil => false
  | GtrCons _ (CtreeNode _ (CtreeLeaf _) _) _ => true
  | GtrCons _ (CtreeNode _ _ (CtreeLeaf _)) _ => true
  | GtrCons _ _ r' => gtr_match0 r'
  end.

Lemma gtr_match0E r : gtr_match0 r = gtr_mem r [:: Gpush].
Proof.
by elim: r => //= bs [] //= t1 t2 t3 r <-; case: t2 => //; case: t3.
Qed.

Fixpoint gtr_match1 r :=
  match r with
  | GtrNil => false
  | GtrCons _ (CtreeNode (CtreeLeaf _) _ _) _ => true
  | GtrCons _ _ r' => gtr_match1 r'
  end.

Lemma gtr_match1E r : gtr_match1 r = gtr_mem r [:: Gskip].
Proof. by elim: r => //= bs [] //= t1 t2 t3 r <-; case: t1. Qed.

Fixpoint gtr_match2 r :=
  match r with
  | GtrNil => false
  | GtrCons (Bpush0 _) (CtreeNode _ (CtreeLeaf _) _) _ => true
  | GtrCons (Bpush1 _) (CtreeNode _ _ (CtreeLeaf _)) _ => true
  | GtrCons _ _ r' => gtr_match2 r'
  end.

Lemma gtr_match2E r : gtr_match2 r = gtr_mem r [:: Gpop0].
Proof.
by elim: r => //= [] [|bs|bs] [] //= t1 t2 t3 r <-; [case: t2 | case: t3].
Qed.

Fixpoint gtr_match3 r :=
  match r with
  | GtrNil => false
  | GtrCons (Bpush0 _) (CtreeNode _ _ (CtreeLeaf _)) _ => true
  | GtrCons (Bpush1 _) (CtreeNode _ (CtreeLeaf _) _) _ => true
  | GtrCons _ _ r' => gtr_match3 r'
  end.

Lemma gtr_match3E r : gtr_match3 r = gtr_mem r [:: Gpop1].
Proof.
by elim: r => //= [] [|bs|bs] [] //= t1 t2 t3 r <-; [case: t3 | case: t2].
Qed.

Definition gtp_0_e := GtreePair GtreeLeaf0 GtreeEmpty.
Definition gtp_1_e := GtreePair GtreeLeaf1 GtreeEmpty.
Definition gtp_2_e := GtreePair GtreeLeaf2 GtreeEmpty.
Definition gtp_3_e := GtreePair GtreeLeaf3 GtreeEmpty.
Definition gtp_01_e := GtreePair GtreeLeaf01 GtreeEmpty.
Definition gtp_12_e := GtreePair GtreeLeaf12 GtreeEmpty.
Definition gtp_13_e := GtreePair GtreeLeaf13 GtreeEmpty.
Definition gtp_23_e := GtreePair GtreeLeaf23 GtreeEmpty.

Definition gtp_e_0 := GtreePair GtreeEmpty GtreeLeaf0.
Definition gtp_e_1 := GtreePair GtreeEmpty GtreeLeaf1.
Definition gtp_e_2 := GtreePair GtreeEmpty GtreeLeaf2.
Definition gtp_e_3 := GtreePair GtreeEmpty GtreeLeaf3.
Definition gtp_e_01 := GtreePair GtreeEmpty GtreeLeaf01.
Definition gtp_e_12 := GtreePair GtreeEmpty GtreeLeaf12.
Definition gtp_e_13 := GtreePair GtreeEmpty GtreeLeaf13.
Definition gtp_e_23 := GtreePair GtreeEmpty GtreeLeaf23.

Definition gtp_0_1 := GtreePair GtreeLeaf0 GtreeLeaf1.
Definition gtp_1_0 := GtreePair GtreeLeaf1 GtreeLeaf0.
Definition gtp_1_2 := GtreePair GtreeLeaf1 GtreeLeaf2.
Definition gtp_2_1 := GtreePair GtreeLeaf2 GtreeLeaf1.
Definition gtp_1_3 := GtreePair GtreeLeaf1 GtreeLeaf3.
Definition gtp_3_1 := GtreePair GtreeLeaf3 GtreeLeaf1.
Definition gtp_2_3 := GtreePair GtreeLeaf2 GtreeLeaf3.
Definition gtp_3_2 := GtreePair GtreeLeaf3 GtreeLeaf2.

Lemma gtree_partition_left t :
  gtree_pair_partition t (GtreePair t GtreeEmpty).
Proof. by move=> w; rewrite gtree_mem_empty; case: ifP. Qed.

Lemma gtree_partition_right t :
  gtree_pair_partition t (GtreePair GtreeEmpty t).
Proof. by move=> w; rewrite gtree_mem_empty; case: ifP. Qed.

Fixpoint gtree_restrict t r {struct t} :=
  match r, t with
  | GtrNil, _ => GtreePair GtreeEmpty t
  | _, GtreeNode t0 t1 t2 t3 =>
    let cont r0 r1 r2 r3 :=
      gtree_cons_pairs t (gtree_restrict t0 r0) (gtree_restrict t1 r1)
                         (gtree_restrict t2 r2) (gtree_restrict t3 r3) in
    gtr_split cont GtrNil GtrNil GtrNil GtrNil r
  | _, GtreeLeaf0 => if gtr_match0 r then gtp_0_e else gtp_e_0
  | _, GtreeLeaf1 => if gtr_match1 r then gtp_1_e else gtp_e_1
  | _, GtreeLeaf2 => if gtr_match2 r then gtp_2_e else gtp_e_2
  | _, GtreeLeaf3 => if gtr_match3 r then gtp_3_e else gtp_e_3
  | _, GtreeLeaf01 =>
    if gtr_match0 r
    then if gtr_match1 r then gtp_01_e else gtp_0_1
    else if gtr_match1 r then gtp_1_0 else gtp_e_01
  | _, GtreeLeaf12 =>
    if gtr_match1 r
    then if gtr_match2 r then gtp_12_e else gtp_1_2
    else if gtr_match2 r then gtp_2_1 else gtp_e_12
  | _, GtreeLeaf13 =>
    if gtr_match1 r
    then if gtr_match3 r then gtp_13_e else gtp_1_3
    else if gtr_match3 r then gtp_3_1 else gtp_e_13
  | _, GtreeLeaf23 =>
    if gtr_match2 r
    then if gtr_match3 r then gtp_23_e else gtp_2_3
    else if gtr_match3 r then gtp_3_2 else gtp_e_23
  | _, GtreeEmpty => empty_gtree_pair
  end.

Let gtpl := gtree_partition_left.
Let gtpr := gtree_partition_right.

Theorem gtree_restrict_partition t r :
  gtree_pair_partition t (gtree_restrict t r).
Proof.
elim: t r => [t0 IHt0 t1 IHt1 t2 IHt2 t3 IHt3|||||||||] r /=;
  case Dr: r => [|bs ct r']; do [exact: gtpr | rewrite -{r' ct bs}Dr];
  by [ case: ifP => _; [apply: gtpl | apply: gtpr]
     | do 2![case: ifP] => _ _ [|[] []]
     | rewrite gtr_split_eq; apply: gtree_cons_pairs_partition].
Qed.

Theorem gtree_mem0_restrict t r w :
  let t' := gtree_pair_sub (gtree_restrict t r) false in
  gtree_mem t' w = gtree_mem t w && gtr_mem r w.
Proof.
pose gm := =^~ (gtr_match0E, gtr_match1E, gtr_match2E, gtr_match3E).
elim: t => /= [t0 IHt0 t1 IHt1 t2 IHt2 t3 IHt3|||||||||] in r w *;
  case Dr: r => [|bs ct r'];
  do [ by rewrite /= gtree_mem_empty ?andbF | rewrite -{bs ct r'}Dr];
  try by do 2?case: ifP => /(pair gm){gm}gm; case: w => [|[][]] //; rewrite !gm.
rewrite gtr_split_eq gtree_mem0_cons_pairs; try exact: gtree_restrict_partition.
by case: w => [|s w]; rewrite // (gtr_mem_gsplit r); case: s => /=.
Qed.

End GtreeRestrict.
