(* (c) Copyright 2006-2018 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From fourcolor Require Import color chromogram gtree ctree.

(******************************************************************************)
(* This is the second phase of a D-reducibility step: adjusting the coloring  *)
(* set match counts to fit the new set of chromograms, thereby removing the   *)
(* colorings whose counts fall to zero.                                       *)
(* Main definitions:                                                          *)
(*  sctree_partition st st0 st1 <-> st[01] is a partition of st : spec_ctree. *)
(*  ctree_partition t pt <-> the contents of pt : ctree_pair is a partition   *)
(*                    of the contents of t : ctree. Match counts need not add *)
(*                    add up.                                                 *)
(*  ctree_restriction == a monomorphic type representing a set of chromogram  *)
(*                    matches to be removed from a ctree. It is equivalent to *)
(*                    seq (bit_stack * gtree), with each pair (bs, gt) in the *)
(*                    sequence standing for the 'matches' (bs, et, w) such    *)
(*                    matchpg bs et w, and gtree_mem gt w.                    *)
(*  ctr_cons bs gt ctr == adds the pair (bs, gt) to ctr : ctree_restriction.  *)
(*  ctr_sub ctr et == the number of matches of the partial color trace et in  *)
(*                    the set repesented by ctr : ctree_restriction.          *)
(* ctr_split k r1 r2 r3 ctr == continuation-passing style splitting of ctr;   *)
(*                    adds to each ctree_restriction r_i the (bs, gt) pairs   *)
(*                    repesenting matches (bs, et, w) that correspond 1-to-1  *)
(*                    to matches (bs', Color_i :: et, s :: w) in ctr, then    *)
(*                    calls k on the resulting triple. Note that ctr_split    *)
(*                    lets us view and eliminate a ctree_restriction as a     *)
(*                    ctree - both denote multisets of traces.                *)
(* ctree_restrict h ct ctr == a ctree_pair partition pt of ct : ctree, whose  *)
(*                    first component is obtained by subtracting the match    *)
(*                    counts in ctr : ctree_restriction from those in ct,     *)
(*                    when the height of ct is h+1.                           *)
(* ctree_decr lf n == decrement a (leaf) ctree lf by n (pop n CtreeLeaf's).   *)
(* ctr_e_decr bs gt e lf == decrement lf by gtree_sub gt bs [:: e]; this is   *)
(*                    the functional specification for the inner loop of      *)
(*                    ctree_restrict.                                         *)
(* ctr_decr k lf1 lf2 lf3 ctr == continuation-passing style implementation of *)
(*                    the base case of ctree_restrict; the three (leaf)       *)
(*                    subtrees of the height 1 ctree are passed explicitly,   *)
(*                    decremented by the respective ctr match counts, and     *)
(*                    passed on to a continuation k.                          *)
(* ctree_leaf_pair lf1 lf2 lf3 lf1' lf2' lf3' == the ctree_pair partition of  *)
(*                    ctree_cons lf_i with first component ctree_cons lf_i'.  *)
(* ctree_cons_pairs pt1 pt2 pt3 == a ctree_pair whose components' subtrees    *)
(*                    are the respective components of pt1, pt2, and pt3.     *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section CtreeRestriction.

Inductive ctree_restriction :=
  CtrNil | CtrCons of bit_stack & gtree & ctree_restriction.

Definition ctr_cons bs t r := if gtree_empty t then r else CtrCons bs t r.

Fixpoint ctr_sub r (et : colseq) {struct r} :=
  if r is CtrCons bs t r' then gtree_sub t bs et + ctr_sub r' et else 0.

Lemma ctr_sub_cons bs t r et :
  ctr_sub (ctr_cons bs t r) et = gtree_sub t bs et + ctr_sub r et.
Proof.
by rewrite /ctr_cons; case: gtree_emptyP => //= ->; rewrite gtree_sub_empty.
Qed.

Section CtrSplit.

Variables (A : Set) (continue : forall r1 r2 r3 : ctree_restriction, A).

Fixpoint ctr_split r1 r2 r3 r {struct r} : A :=
  match r with
  | CtrNil => continue r1 r2 r3
  | CtrCons bs (GtreeNode t0 t1 t2 t3) r' =>
      let addr bs t r' := if t is GtreeEmpty then r' else CtrCons bs t r' in
      let dorec r2' r3' :=
        if t0 is GtreeEmpty then ctr_split (addr bs t1 r1) r2' r3' r' else
        let r2'' := CtrCons (Bpush0 bs) t0 r2' in
        let r3'' := CtrCons (Bpush1 bs) t0 r3' in
        ctr_split (addr bs t1 r1) r2'' r3'' r' in
      match bs with
      | Bstack0 => dorec r2 r3
      | Bpush0 bs' => dorec (addr bs' t2 r2) (addr bs' t3 r3)
      | Bpush1 bs' => dorec (addr bs' t3 r2) (addr bs' t2 r3)
      end
  | CtrCons _ _ r' => ctr_split r1 r2 r3 r'
  end.

Lemma ctr_split_some bs t0 t1 t2 t3 r1 r2 r3 r :
 let cons_pop t t' r' :=
   match bs with
   | Bstack0 => r'
   | Bpush0 bs' => ctr_cons bs' t r'
   | Bpush1 bs' => ctr_cons bs' t' r'
   end in
 ctr_split r1 r2 r3 (CtrCons bs (GtreeNode t0 t1 t2 t3) r) =
 ctr_split (ctr_cons bs t1 r1) (ctr_cons (Bpush0 bs) t0 (cons_pop t2 t3 r2))
                               (ctr_cons (Bpush1 bs) t0 (cons_pop t3 t2 r3)) r.
Proof.
by case: bs => [|bs|bs] /=; rewrite !fold_gtree_empty /ctr_cons; case: ifP.
Qed.

End CtrSplit.

Let csplit r e :=
  let rk t1 t2 t3 := palette CtrNil t1 t2 t3 e in
  ctr_split rk CtrNil CtrNil CtrNil r.

Lemma ctr_split_eq A rk r :
 @ctr_split A rk CtrNil CtrNil CtrNil r
   = rk (csplit r Color1) (csplit r Color2) (csplit r Color3).
Proof.
rewrite /csplit; move: CtrNil {2 4 6 8}CtrNil {3 6 9 12}CtrNil.
elim: r  => [|bs t r IHr] r1 r2 r3 //.
by case: t => // *; rewrite ?ctr_split_some; apply: IHr.
Qed.

Lemma ctr_sub_csplit r e et :
  ctr_sub (csplit r e) et = (if size et == 0 then 0 else ctr_sub r (e :: et)).
Proof.
case Det: {2}et => [|e' et'] /=.
  rewrite {et}Det; elim: {r e}(csplit r e) => //= [bs t r IHr].
  by rewrite IHr addn0; case: t.
transitivity (ctr_sub (csplit CtrNil e) et + ctr_sub r (e :: et)); last first.
  by case: (e).
rewrite /csplit /=; move: {2 4}CtrNil {3 6}CtrNil {4 8}CtrNil.
elim: r => [|bs t r IHr] r1 r2 r3; first by rewrite /= addn0.
have sub0: (forall s s' w, ~~ gtree_mem t [:: s, s' & w]) ->
  gtree_sub t bs (e :: et) = 0.
- rewrite {IHr}Det /gtree_sub; move: (gtree_mem t) => st st0.
  by case: e e' => [] // [] //=;
     do 3![rewrite ?match_count_0 //; case: bs => //= bs].
case: t sub0; do [ move=> t0 t1 t2 t3 _; rewrite ctr_split_some {}IHr
                 | by move=> sub0; rewrite /= {}IHr {}sub0 //; case ].
rewrite /= addnA -2!(addnC (ctr_sub r (e :: et))); congr (_ + _); rewrite addnC.
have mc_eta := @match_count_eq [eta gtree_mem _] (gtree_mem _) (frefl _).
case: e; rewrite //= ctr_sub_cons /gtree_sub /= ?mc_eta //;
  by case: bs => *; rewrite ?ctr_sub_cons /= ?mc_eta ?addnA ?addn0.
Qed.

Fixpoint ctree_decr lf n {struct n} :=
  match n, lf with
  | n'.+1, CtreeLeaf lf' => ctree_decr lf' n'
  | _, _ => lf
  end.

Lemma ctree_val_decr m n :
  ctree_decr (ctree_leaf_of m) n = ctree_leaf_of (m - n).
Proof. by elim: n m => [|n IHn] [|m] //; apply: IHn. Qed.

Lemma ctree_no_decr t n : ~~ ctree_leaf t -> ctree_decr t n = t.
Proof. by case: t n => [t1 t2 t3 | lf |] [|n]. Qed.

Section CtrDecr.

Variables (A : Set) (cont : forall lf1 lf2 lf3 : ctree, A).

(* The outermost match in dlf ensures that thunks are forced under a lazy     *)
(* evaluation strategy.                                                       *)
Definition ctr_decr := Eval lazy beta zeta in
  let dlf lf klf := if lf is CtreeLeaf lf' then klf lf' else klf lf in
  let dlf1 lfk lf1 lf2 lf3 := dlf lf1 (fun lf1' => lfk lf1' lf2 lf3) in
  let dlf2 lfk lf1 lf2 lf3 := dlf lf2 (fun lf2' => lfk lf1 lf2' lf3) in
  let dlf3 lfk lf1 lf2 lf3 := dlf lf3 (fun lf3' => lfk lf1 lf2 lf3') in
  fix ctr_decr (lf1 lf2 lf3 : ctree) (r : ctree_restriction) {struct r} : A :=
  match r with
  | CtrNil => cont lf1 lf2 lf3
  | CtrCons bs t r' =>
    let lfk lf1' lf2' lf3' := ctr_decr lf1' lf2' lf3' r' in
    match t, bs with
    | GtreeLeaf0,  _        => dlf2 (dlf3 lfk) lf1 lf2 lf3
    | GtreeLeaf1,  _        => dlf1 lfk lf1 lf2 lf3
    | GtreeLeaf2,  Bpush0 _ => dlf2 lfk lf1 lf2 lf3
    | GtreeLeaf2,  Bpush1 _ => dlf3 lfk lf1 lf2 lf3
    | GtreeLeaf3,  Bpush0 _ => dlf3 lfk lf1 lf2 lf3
    | GtreeLeaf3,  Bpush1 _ => dlf2 lfk lf1 lf2 lf3
    | GtreeLeaf01, _        => dlf1 (dlf2 (dlf3 lfk)) lf1 lf2 lf3
    | GtreeLeaf12, Bstack0  => dlf1 lfk lf1 lf2 lf3
    | GtreeLeaf12, Bpush0 _ => dlf1 (dlf2 lfk) lf1 lf2 lf3
    | GtreeLeaf12, Bpush1 _ => dlf1 (dlf3 lfk) lf1 lf2 lf3
    | GtreeLeaf13, Bstack0  => dlf1 lfk lf1 lf2 lf3
    | GtreeLeaf13, Bpush0 _ => dlf1 (dlf3 lfk) lf1 lf2 lf3
    | GtreeLeaf13, Bpush1 _ => dlf1 (dlf2 lfk) lf1 lf2 lf3
    | GtreeLeaf23, Bpush0 _ => dlf2 (dlf3 lfk) lf1 lf2 lf3
    | GtreeLeaf23, Bpush1 _ => dlf2 (dlf3 lfk) lf1 lf2 lf3
    | _,           _        => lfk lf1 lf2 lf3
    end
  end.

Definition ctr_e_decr bs t e lf := ctree_decr lf (gtree_sub t bs [:: e]).

Lemma ctr_decr_some lf1 lf2 lf3 bs t r :
   let cde := ctr_e_decr bs t in
 ctr_decr lf1 lf2 lf3 (CtrCons bs t r)
   = ctr_decr (cde Color1 lf1) (cde Color2 lf2) (cde Color3 lf3) r.
Proof.
case: t; by [ move=> t0 t1 t2 t3; rewrite /ctr_e_decr !gtree_sub_node_0
            | case: lf1 => //; case: bs => // *; case: lf2; case: lf3 ].
Qed.

End CtrDecr.

Let cdecr e := ctr_decr (fun ct1 ct2 ct3 => palette CtreeEmpty ct1 ct2 ct3 e).

Lemma ctr_decr_eq A lfk lf1 lf2 lf3 r :
   let cdecr_r e := cdecr e lf1 lf2 lf3 r in
 @ctr_decr A lfk lf1 lf2 lf3 r
   = lfk (cdecr_r Color1) (cdecr_r Color2) (cdecr_r Color3).
Proof.
rewrite /cdecr; elim: r => // bs t r IHr in lf1 lf2 lf3 *.
by rewrite !ctr_decr_some IHr.
Qed.

Lemma ctree_proper_leaf_of_val lf :
  ctree_proper 0 lf -> lf = ctree_leaf_of (ctree_sub lf [::]).
Proof. by elim: lf => //= lf IHlf /IHlf<-. Qed.

Lemma cdecr_leaf e lf1 lf2 lf3 r :
   let t := ctree_cons lf1 lf2 lf3 in let et := [:: e] in
   ctree_proper 1 t ->
 cdecr e lf1 lf2 lf3 r = ctree_leaf_of (ctree_sub t et - ctr_sub r et).
Proof.
move=> /= t_ok.
elim: r => [|bs t r IHr] in lf1 lf2 lf3 t_ok *;
  have{t_ok} Dlf := ctree_proper_leaf_of_val (ctree_proper_sel _ t_ok).
- by rewrite /= subn0 ctree_sub_cons; case: e (Dlf e); rewrite ctree_sel_cons.
rewrite /cdecr !ctr_decr_some -/(cdecr e) {}IHr /=.
congr ctree_leaf_of; move/(_ e): Dlf.
  rewrite ctree_sel_cons 2!ctree_sub_cons /ctr_e_decr.
  by case: e => //= ->; rewrite ctree_val_decr !ctree_sub_leaf_of subnDA.
do [apply: ctree_cons_proper; move: Dlf]; 
     [move/(_ Color1) | move/(_ Color2) | move/(_ Color3)];
  rewrite ctree_sel_cons /ctr_e_decr /= => ->;
  by rewrite ctree_val_decr; apply: ctree_leaf_of_proper.
Qed.

(* The let and outermost match ensure that thunks are forced under a lazy     *)
(* evaluation strategy.                                                       *)
Definition ctree_cons_pairs pt1 pt2 pt3 :=
  let: CtreePair t1 t1' := pt1 in
  let: CtreePair t2 t2' := pt2 in
  let: CtreePair t3 t3' := pt3 in
  let t := CtreeNode t1 t2 t3 in let t' := CtreeNode t1' t2' t3' in
  match ctree_empty_node t, ctree_empty_node t' with
  | true, true => CtreePair CtreeEmpty CtreeEmpty
  | true, false => CtreePair CtreeEmpty t'
  | false, true => CtreePair t CtreeEmpty
  | false, false => CtreePair t t'
  end.

Lemma ctree_cons_pairs_spec t1 t1' t2 t2' t3 t3' :
 ctree_cons_pairs (CtreePair t1 t1') (CtreePair t2 t2') (CtreePair t3 t3')
   = CtreePair (ctree_cons t1 t2 t3) (ctree_cons t1' t2' t3').
Proof. by rewrite 2!ctree_cons_spec /=; do 2!case: ifP => _. Qed.

Definition sctree_partition (st st' st'' : colseq -> bool) :=
  forall et, (if st et then eqb else orb) (st' et) (st'' et) = false.

Definition ctree_partition t (pt : ctree_pair) :=
  let (t', t'') := pt in
  sctree_partition (ctree_mem t) (ctree_mem t') (ctree_mem t'').

Lemma ctree_cons_pairs_partition t1 t2 t3 pt1 pt2 pt3 :
    ctree_partition t1 pt1 ->
    ctree_partition t2 pt2 ->
    ctree_partition t3 pt3 ->
  ctree_partition (CtreeNode t1 t2 t3) (ctree_cons_pairs pt1 pt2 pt3).
Proof.
move: pt1 pt2 pt3 => [t1' t1''] [t2' t2''] [t3' t3''].
rewrite ctree_cons_pairs_spec /= /ctree_mem => ppt1 ppt2 ppt3 et.
by rewrite 2!ctree_sub_cons; case: et => [|[] et] /=.
Qed.

Lemma ctree_sub0_cons_pairs pt1 pt2 pt3 et :
   let cp0 pt := ctree_pair_sub pt false in
 ctree_sub (cp0 (ctree_cons_pairs pt1 pt2 pt3)) et
   = ctree_sub (CtreeNode (cp0 pt1) (cp0 pt2) (cp0 pt3)) et.
Proof.
move: pt1 pt2 pt3 => [t1 t1'] [t2 t2'] [t3 t3'].
by rewrite ctree_cons_pairs_spec /= ctree_sub_cons; case: et.
Qed.

(* The let and outermost match ensure that thunks are forced under a lazy     *)
(* evaluation strategy.                                                       *)
Definition ctree_leaf_pair lf1 lf2 lf3 lf1' lf2' lf3' :=
  let lf' := CtreeNode lf1' lf2' lf3' in
  match lf' with
  | CtreeNode CtreeEmpty CtreeEmpty CtreeEmpty =>
    CtreePair lf1' (ctree_cons lf1 lf2 lf3)
  | CtreeNode CtreeEmpty CtreeEmpty _ =>
    CtreePair lf' (ctree_cons lf1 lf2 lf1')
  | CtreeNode CtreeEmpty _ CtreeEmpty =>
    CtreePair lf' (ctree_cons lf1 lf1' lf3)
  | CtreeNode CtreeEmpty _ _ =>
    CtreePair lf' (ctree_cons lf1 lf1' lf1')
  | CtreeNode _ CtreeEmpty CtreeEmpty =>
    CtreePair lf' (ctree_cons lf2' lf2 lf3)
  | CtreeNode _ CtreeEmpty _ =>
    CtreePair lf' (ctree_cons lf2' lf2 lf2')
  | CtreeNode _ _ CtreeEmpty =>
    CtreePair lf' (ctree_cons lf3' lf3' lf3)
  | _ =>
    CtreePair lf' CtreeEmpty
  end.

Lemma ctree_leaf_pair_spec lf1 lf2 lf3 lf1' lf2' lf3' :
  let if_e lf lf' := if ctree_empty lf' then lf else CtreeEmpty in
  let t' := ctree_cons lf1' lf2' lf3' in
  let t'' := ctree_cons (if_e lf1 lf1') (if_e lf2 lf2') (if_e lf3 lf3') in
  ctree_leaf_pair lf1 lf2 lf3 lf1' lf2' lf3' = CtreePair t' t''.
Proof. by case: lf1'; case: lf2'; case: lf3'. Qed.

Fixpoint ctree_restrict (h : nat) (t : ctree) r {struct h} :=
  match r, h, t with
  | CtrNil, _, _ => CtreePair t CtreeEmpty
  | _, h'.+1, CtreeNode t1 t2 t3 =>
    let rh' := ctree_restrict h' in
    let rk r1 r2 r3 := ctree_cons_pairs (rh' t1 r1) (rh' t2 r2) (rh' t3 r3) in
    ctr_split rk CtrNil CtrNil CtrNil r
  | _, 0, CtreeNode lf1 lf2 lf3 =>
    ctr_decr (ctree_leaf_pair lf1 lf2 lf3) lf1 lf2 lf3 r
  | _, _, _ =>
    ctree_empty_pair
  end.

Lemma ctree_restrict_correct h t r :
   ctree_proper h.+1 t ->
   let pt := ctree_restrict h t r in
 [/\ forall b, ctree_proper h.+1 (ctree_pair_sub pt b),
     ctree_partition t pt
   & forall et, ctree_sub (ctree_pair_sub pt false) et
                  = ctree_sub t et - ctr_sub r et].
Proof.
elim: h => [|h' IHh] in t r *.
  move Dpt: (ctree_restrict 0 t r) => pt t_ok.
  case Dt: t t_ok Dpt => [lf1 lf2 lf3|lf|] lf_ok //.
    case Dr: r => [/= | bs gt r']; last rewrite /ctree_restrict -{bs gt r'}Dr.
      by move <-; split=> [[] | et | et] //; [case: ifP | rewrite subn0].
    rewrite ctr_decr_eq ctree_leaf_pair_spec.
    have Dlf := ctree_proper_leaf_of_val (ctree_proper_sel _ lf_ok).
    have [[-> _ _ _] id_t] := (lf_ok, ctree_cons_spec lf1 lf2 lf3 : _ = _).
    rewrite -id_t in lf_ok; rewrite !(cdecr_leaf _ r lf_ok) !ctree_sub_cons /=.
    move: {Dlf}(Dlf Color1) (Dlf Color2) (Dlf Color3) => /=.
    move: (ctree_sub lf1 _) (ctree_sub lf2 _) (ctree_sub lf3 _) => n1 n2 n3.
    move=> Dlf1 Dlf2 Dlf3 <- {pt}; split=> [|et|et].
    - case=> /=; last by apply: ctree_cons_proper; apply: ctree_leaf_of_proper.
      rewrite Dlf1 Dlf2 Dlf3; apply: ctree_cons_proper;
        by case: ifP => // _; apply: ctree_leaf_of_proper.
    - rewrite !ctree_mem_cons /= /ctree_mem; case: et => [|[] et] //=.
      + rewrite {}Dlf1; case: n1 => [|n1] //; move: (_ - _) => m1.
        by rewrite 2!ctree_sub_leaf_of; case: et; case: m1.
      + rewrite {}Dlf2; case: n2 => [|n2] //; move: (_ - _) => m2.
        by rewrite 2!ctree_sub_leaf_of; case: et; case: m2.
      rewrite {}Dlf3; case: n3 => [|n3] //; move: (_ - _) => m3.
      by rewrite 2!ctree_sub_leaf_of; case: et; case: m3.
    rewrite /= ctree_sub_cons /=; case: et => [|[] et] //=;
      by rewrite ?Dlf1 ?Dlf2 ?Dlf3 !ctree_sub_leaf_of; case: et.
  move=> Dpt; have{Dpt} -> /=: pt = ctree_empty_pair by case: r Dpt.
  by split; case.
case: t => // [t1 t2 t3|] t_ok; last first.
  have <-: ctree_empty_pair = ctree_restrict h'.+1 CtreeEmpty r by case: r.
  by split; case.
move Dpt: (ctree_restrict _ _ r) => /= pt.
case Dr: r Dpt => [/= | bs gt r']; last rewrite -{bs gt r'}Dr.
  by move=> <-{pt}; split=> [[] //|et|et]; [case: ifP | rewrite subn0].
rewrite ctr_split_eq.
have{IHh} IHe e := IHh _ (csplit r e) (ctree_proper_sel e t_ok).
move: {IHe}(IHe Color1) (IHe Color2) (IHe Color3) => /=.
case: (ctree_restrict _ t1 _) => [t1' t1''].
case: (ctree_restrict _ t2 _) => [t2' t2''].
case: (ctree_restrict _ t3 _) => [t3' t3''].
move=> [t1ok ppt1 Dt1'] [t2ok ppt2 Dt2'] [t3ok ppt3 Dt3'] <- {pt};
split=> [b0||et]; first 2 [exact: ctree_cons_pairs_partition].
  rewrite ctree_cons_pairs_spec.
  by case: b0 (t1ok b0) (t2ok b0) (t3ok b0) (ctree_cons_proper) => /=; auto.
rewrite ctree_sub0_cons_pairs {t1ok ppt1 t2ok ppt2 t3ok ppt3}.
case: et => [|e et] //=; move: {Dt1' Dt2' Dt3'}(Dt1' et) (Dt2' et) (Dt3' et).
rewrite !ctr_sub_csplit /=; case: et => [|e' et'] /= Et1' Et2' Et3';
  case: e {t_ok}(ctree_proper_sel e t_ok) => //=.
- by rewrite {}Et1'; case: t1.
- by rewrite {}Et2'; case: t2.
by rewrite {}Et3'; case: t3.
Qed.

End CtreeRestriction.
