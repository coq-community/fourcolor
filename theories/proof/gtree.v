(* (c) Copyright 2006-2018 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From fourcolor Require Import color chromogram.

(******************************************************************************)
(*   Sets of partial chromograms are stored as 4-way trees, much like partial *)
(* edge traces are stored in ctrees.                                          *)
(*        gtree == the type of (chromo)gram trees; unlike ctrees, gtrees      *)
(*                 never record multiplicities.                               *)
(*   GtreeEmpty == the empty gtree.                                           *)
(*   GtreeNode t0 t1 t2 t3 == a gtree node, where the t_i's store the 'grams  *)
(*                 that follow a Gskip, Gpush, Gpop0, Gpop1, respectively.    *)
(*   GtreeLeaf[i|ij] == the gtree that stores the partial 'grams containing   *)
(*                 just symbol i (or i or j) in Gskip, Gpush, Gpop0, Gpop1.   *)
(*                 Only 8 combinations are needed.                            *)
(*  gtree_mem t w <=> t : gtree contains the partial chromogram w.            *)
(*     spec_ctree := pred colseq, the type of ctree specifications.           *)
(*     spec_gtree := pred chromogram, the type of gtree specifications.       *)
(*  has_match bs ct w <=> there exists a partial trace et, satisfying ct :    *)
(*                 spec_ctree and such that matchpg bs et w, i.e., matching w *)
(*                 in the open chord context represented by bs : bit_stack.   *)
(*  match_count st bs et == the number of partial chromograms w satisfying    *)
(*                 spec_gtree st, and matchpg bs et w.                        *)
(*  gtree_sub t bs et == the number of partial chromograms w in the gtree t   *)
(*                 that match et and bs (such that matchpg bs et w).          *)
(*  gtree_empty4 t <=> t is a gtree node with four empty subtrees.            *)
(*     gtree_pair == a monomorphic type equivalent to gtree * gtree; this is  *)
(*                 the return type of the restrict operation.                 *)
(* empty_gtree_pair == a GtreePair of GtreeEmpty's.                           *)
(* gtree_pair_sub pt b == the b'th component of pt : gtree_pair for b : bool. *)
(* sgtree_partition st st0 st1 <-> st[01] : spec_gtree are a partition of st, *)
(*                 i.e., st0 and st1 are exclusive and st w = st0 w || st1 w. *)
(* gtree_pair_partition t pt <-> membership in components of pt : gtree_pair  *)
(*                 is a partition of membership in t : gtree.                 *)
(* gtree_cons_pairs pt0 pt1 pt2 pt3 == a gtree_pair of GtreeNode's whose      *)
(*                 subtrees are the components of the pt[0-3], respectively.  *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive gtree :=
  | GtreeNode of gtree & gtree & gtree & gtree
  | GtreeLeaf0
  | GtreeLeaf1
  | GtreeLeaf2
  | GtreeLeaf3
  | GtreeLeaf01
  | GtreeLeaf12
  | GtreeLeaf13
  | GtreeLeaf23
  | GtreeEmpty.

(* The following classifiers are effective. *)

Definition gtree_empty t := if t is GtreeEmpty then true else false.

Lemma fold_gtree_empty A (ve vne : A) t :
  (if t is GtreeEmpty then ve else vne) = (if gtree_empty t then ve else vne).
Proof. by case: t. Qed.

Lemma gtree_emptyP {t} : reflect (t = GtreeEmpty) (gtree_empty t).
Proof. by case: t; constructor. Qed.

(* Only the membership function needs to be defined on trees; enumerating *)
(* matches can be deifned based solely on the characteristic function.    *)

Fixpoint gtree_mem t (w : chromogram) {struct w} :=
  match t, w with
  | GtreeNode t0 t1 t2 t3, s :: w' =>
    gtree_mem (gram_symbol_rec t0 t1 t2 t3 s) w'
  | GtreeLeaf0,  [:: Gpush] => true
  | GtreeLeaf1,  [:: Gskip] => true
  | GtreeLeaf2,  [:: Gpop0] => true
  | GtreeLeaf3,  [:: Gpop1] => true
  | GtreeLeaf01, [:: Gpush] => true
  | GtreeLeaf01, [:: Gskip] => true
  | GtreeLeaf12, [:: Gskip] => true
  | GtreeLeaf12, [:: Gpop0] => true
  | GtreeLeaf13, [:: Gskip] => true
  | GtreeLeaf13, [:: Gpop1] => true
  | GtreeLeaf23, [:: Gpop0] => true
  | GtreeLeaf23, [:: Gpop1] => true
  | _, _ => false
  end.

(* Functions that check for / count matches for arbitrary predicates. *)
(* Could move to bare chromograms, or to a separate ``match'' file.   *)

Definition spec_ctree := pred colseq.

Fixpoint has_match bs (ct : spec_ctree) (w : chromogram) {struct w} :=
  let sct e et := ct (e :: et) in
  match w with
  | [::] =>
    ct [::]
  | Gpush :: w' =>
    has_match (Bpush0 bs) (sct Color2) w'
    || has_match (Bpush1 bs) (sct Color3) w'
  | Gskip :: w' =>
    has_match bs (sct Color1) w'
  | Gpop0 :: w' =>
    match bs with
    | Bpush0 bs' => has_match bs' (sct Color2) w'
    | Bpush1 bs' => has_match bs' (sct Color3) w'
    | _ => false
    end
  | Gpop1 :: w' =>
    match bs with
    | Bpush0 bs' => has_match bs' (sct Color3) w'
    | Bpush1 bs' => has_match bs' (sct Color2) w'
    | _ => false
    end
  end.

Lemma has_matchP bs (ct : spec_ctree) w :
  reflect (exists2 et, ct et & matchpg bs et w) (has_match bs ct w).
Proof.
elim: w => [|s w IHw] /= in bs ct *.
  by apply: (iffP idP) => [|[[] //]]; exists [::].
case Ds: s; rewrite /= -/colseq.
- case: (IHw) => [wMe2 | not_wMe2].
    by left; have [et] := wMe2; exists (Color2 :: et).
  apply: (iffP (IHw _ _)) => [[et] | []]; first by exists (Color3 :: et).
  by case=> [|[] et *] //; first case: not_wMe2; exists et.
- apply: (iffP (IHw _ _)) => [[et] | []]; first by exists (Color1 :: et).
  by case=> [|[]] // et *; exists et.
- case: bs => [|bs|bs]; first by right=> [] [] [|[]].
  + apply: (iffP (IHw _ _)) => [[et] | []]; first by exists (Color2 :: et).
    by case=> [|[]] // et *; exists et.
  apply: (iffP (IHw _ _)) => [[et] | []]; first by exists (Color3 :: et).
  by case=> [|[]] // et *; exists et.
case: bs => [|bs|bs]; first by right=> [] [] [|[]].
+ apply: (iffP (IHw _ _)) => [[et] | []]; first by exists (Color3 :: et).
  by case=> [|[]] // et *; exists et.
apply: (iffP (IHw _ _)) => [[et] | []]; first by exists (Color2 :: et).
by case=> [|[]] // et *; exists et.
Qed.
Arguments has_matchP {bs ct w}.

Definition spec_gtree := pred chromogram.

Fixpoint match_count (st : spec_gtree) bs (et : colseq) {struct et} :=
  let sub_st s w := st (s :: w) in
  match et with
  | [::] => if st [::] then 1 else 0
  | Color0 :: _ => 0
  | Color1 :: et' => match_count (sub_st Gskip) bs et'
  | Color2 :: et' =>
    let sub_pop := match bs with
    | Bstack0 => 0
    | Bpush0 bs' => match_count (sub_st Gpop0) bs' et'
    | Bpush1 bs' => match_count (sub_st Gpop1) bs' et' end in
    match_count (sub_st Gpush) (Bpush0 bs) et' + sub_pop
  | Color3 :: et' =>
    let sub_pop := match bs with
    | Bstack0 => 0
    | Bpush0 bs' => match_count (sub_st Gpop1) bs' et'
    | Bpush1 bs' => match_count (sub_st Gpop0) bs' et' end in
    match_count (sub_st Gpush) (Bpush1 bs) et' + sub_pop
  end.

Definition gtree_sub t := match_count (gtree_mem t).

Lemma match_countP (st : spec_gtree) bs et :
  reflect (exists2 w, st w & matchpg bs et w) (match_count st bs et != 0).
Proof.
elim: et => /= [|e et IHet] in st bs *.
  case: ifP => st0; constructor; first by exists [::].
  by case=> [] [|[]] //; rewrite st0.
case: e; try (rewrite addn_eq0 negb_and; case: (IHet) => [pushMet | ];
                first by [left; have [w] := pushMet; exists (Gpush :: w)];
              case: bs => [|bs|bs] not_pushMet);
  do [right | apply: (iffP (IHet _ _)) => [[w]|]];
  by [exists (Gpop0 :: w) | exists (Gpop1 :: w) | exists (Gskip :: w)
     | case=> [] [|[] w] // *; by [exists w | case: not_pushMet; exists w]].
Qed.
Arguments match_countP {st bs et}.

(* The gtree_empty4 function serves two purposes :                          *)
(*   - it allows contraction of empty trees, and reuse of unmodified trees  *)
(*   - it interlocks the tree computation, so that trees do NOT contain     *)
(*     thunks.                                                              *)
(* The latter point implies that the function must NOT short-circuit tests  *)

Definition gtree_empty_and t b :=
  match t, b with
  | _, false => false
  | GtreeEmpty, true => true
  | _, _ => false
  end.

Lemma gtree_empty_and_spec t b : gtree_empty_and t b = gtree_empty t && b.
Proof. by case: b; case: t. Qed.

Definition gtree_empty4 t :=
  if t is GtreeNode t0 t1 t2 t3 then
    gtree_empty_and t0 (gtree_empty_and t1 (gtree_empty_and t2
                                                            (gtree_empty t3)))
  else false.

Inductive are_4_GtreeEmpty : forall t0 t1 t2 t3 : gtree, Prop :=
  GtreeEmpty4 :
    are_4_GtreeEmpty GtreeEmpty GtreeEmpty GtreeEmpty GtreeEmpty.

Lemma gtree_empty4P {t0 t1 t2 t3} :
  reflect (are_4_GtreeEmpty t0 t1 t2 t3)
          (gtree_empty4 (GtreeNode t0 t1 t2 t3)).
Proof.
rewrite /gtree_empty4 3!gtree_empty_and_spec.
by apply: (iffP and4P) => [[]|[]//]; do 4!move/gtree_emptyP->.
Qed.

(* The restriction operation returns a partition of a gram tree into a pair *)
(* of gram trees.                                                           *)

Inductive gtree_pair := GtreePair of gtree & gtree.

Definition empty_gtree_pair := GtreePair GtreeEmpty GtreeEmpty.

Definition gtree_pair_sub pt b :=
  let: GtreePair t0 t1 := pt in if b then t1 else t0.

Definition sgtree_partition (st st' st'' : spec_gtree) :=
  forall w, (if st w then eqb else orb) (st' w) (st'' w) = false.

Definition gtree_pair_partition t pt :=
  let: GtreePair t0 t1 := pt in
  sgtree_partition (gtree_mem t) (gtree_mem t0) (gtree_mem t1).

Lemma match_count_0 st :
  (forall w, ~~ st w) -> forall bs et, match_count st bs et = 0.
Proof.
move=> st0 bs et; elim: et => [|e et IHet] in st bs st0 *.
  by rewrite /= (negPf (st0 _)).
by case: e; rewrite /= ?IHet //; case: bs => * //=; rewrite IHet.
Qed.

Lemma gtree_mem_empty w : gtree_mem GtreeEmpty w = false.
Proof. by case: w. Qed.

Lemma gtree_sub_empty bs et : gtree_sub GtreeEmpty bs et = 0.
Proof. by apply: match_count_0 => w; rewrite gtree_mem_empty. Qed.

Lemma gtree_sub_node_0 bs t0 t1 t2 t3 (et : colseq) :
  (size et).-1 = 0 -> gtree_sub (GtreeNode t0 t1 t2 t3) bs et = 0.
Proof.
case: et => [|e [|e' et]] // _; rewrite /gtree_sub /=.
have Htf t: (if t is GtreeEmpty then false else false) = false by case: t.
by rewrite !Htf; case: e => //; case: bs.
Qed.

Lemma match_count_eq (st st' : spec_gtree) :
  st =1 st' -> match_count st =2 match_count st'.
Proof.
move=> eq_st bs et; elim: et => [|e et IHet] in st st' eq_st bs *.
  by rewrite /= eq_st.
case: e => //=; try (case: bs => *; congr (_ + _));
  by apply: IHet => w; apply: eq_st.
Qed.

Lemma match_count_partition st st' st'' :
    sgtree_partition st st' st'' ->
    forall bs et,
  match_count st bs et = match_count st' bs et + match_count st'' bs et.
Proof.
move=> eq_st bs et; elim: et => [|e et IHet] in st st' st'' eq_st bs *.
  by have /= := eq_st [::]; case: (st _); case: (st' _); case: (st'' _).
case: e => //=;
  try (rewrite addnCA -addnA addnCA addnA; case: bs => *; congr (_ + _));
  by apply: IHet => w; apply: eq_st.
Qed.

Definition gtree_cons_pairs t pt0 pt1 pt2 pt3 :=
  let: GtreePair t'0 t''0 := pt0 in
  let: GtreePair t'1 t''1 := pt1 in
  let: GtreePair t'2 t''2 := pt2 in
  let: GtreePair t'3 t''3 := pt3 in
  let mkpair0 t' t'' :=
    if gtree_empty4 t' then GtreePair t'0 t else
    if gtree_empty4 t'' then GtreePair t t''0 else GtreePair t' t'' in
  mkpair0 (GtreeNode t'0 t'1 t'2 t'3) (GtreeNode t''0 t''1 t''2 t''3).

Lemma gtree_cons_pairs_partition t0 t1 t2 t3 pt0 pt1 pt2 pt3 :
    gtree_pair_partition t0 pt0 -> gtree_pair_partition t1 pt1 ->
    gtree_pair_partition t2 pt2 -> gtree_pair_partition t3 pt3 ->
    let t := GtreeNode t0 t1 t2 t3 in
  gtree_pair_partition t (gtree_cons_pairs t pt0 pt1 pt2 pt3).
Proof.
case: pt0 pt1 pt2 pt3 => [t'0 t''0] [t'1 t''1] [t'2 t''2] [t'3 t''3] *.
rewrite /gtree_cons_pairs.
do 2![case: gtree_empty4P => [[] w| _];
  first by rewrite gtree_mem_empty; case: ifP].
by case=> [|[]].
Qed.

Lemma gtree_mem0_cons_pairs t0 t1 t2 t3 pt0 pt1 pt2 pt3 :
    gtree_pair_partition t0 pt0 -> gtree_pair_partition t1 pt1 ->
    gtree_pair_partition t2 pt2 -> gtree_pair_partition t3 pt3 ->
  let sub0 pt := gtree_pair_sub pt false in
  let t := GtreeNode t0 t1 t2 t3 in
  let t' := GtreeNode (sub0 pt0) (sub0 pt1) (sub0 pt2) (sub0 pt3) in
  gtree_mem (sub0 (gtree_cons_pairs t pt0 pt1 pt2 pt3)) =1 gtree_mem t'.
Proof.
move: pt0 pt1 pt2 pt3 => /= [t'0 t''0] [t'1 t''1] [t'2 t''2] [t'3 t''3].
rewrite /gtree_cons_pairs; case: gtree_empty4P => [[] * [|[] []] // | _].
case: gtree_empty4P => [[] | ] //= ppt0 ppt1 ppt2 ppt3 [|[] w] //=.
- by case: gtree_mem (ppt0 w); case: gtree_mem; case: w.
- by case: gtree_mem (ppt1 w); case: gtree_mem; case: w.
- by case: gtree_mem (ppt2 w); case: gtree_mem; case: w.
- by case: gtree_mem (ppt3 w); case: gtree_mem; case: w.
Qed.
