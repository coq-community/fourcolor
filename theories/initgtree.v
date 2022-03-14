(* (c) Copyright 2006-2018 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From fourcolor Require Import color chromogram gtree dyck.

(******************************************************************************)
(*   Creation of the initial (full) chromogram tree for a given ring size     *)
(* using dynamic programming, similarly to the initial coloring trace tree.   *)
(*   Main definitions:                                                        *)
(* gtree_init_tree h == the tree storing all balanced partial chromograms     *)
(*                  for a given ring size h.                                  *)
(* init_gtree_spec h == the specification (membership predicate) for          *)
(*                  of gtree_init_tree h.                                     *)
(*   gtree_table := seq gtree_pair, the type of tables storing subtrees of a  *)
(*                  given height, for a given ring size. Only the length of   *)
(*                  the tables depends on the ring size (unlike ctree's).     *)
(*  gtree_table_sub tab d b == the gtree in tab : gtree_table storing partial *)
(*                  chromograms that are consistent with a context of d open  *)
(*                  chords and parity b - the w s.t. cgram d b w is balanced. *)
(* init_gtree_h1 == the table of all trees of height 1.                       *)
(* gtree_init_table n h == a table of gtrees of height h+1 and of length at   *)
(*                  least h+1.                                                *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section InitialGtree.

Definition gtree_table := seq gtree_pair.

Definition init_gtree_h1 : gtree_table :=
  [:: GtreePair GtreeLeaf01 GtreeLeaf0;
      GtreePair GtreeLeaf13 GtreeLeaf12;
      GtreePair GtreeLeaf23 GtreeLeaf23].

Definition gtree_merge_pairs pt0 pt1 pt2 :=
  let: GtreePair t0 t0' := pt0 in
  let: GtreePair t1 t1' := pt1 in
  let: GtreePair t2 t3 := pt2 in
  GtreePair (GtreeNode t0 t1' t2 t3) (GtreeNode t0' t1 t3 t2).

Fixpoint gtree_merge_line pt0 pt1 pt2 (lpt : gtree_table) d {struct d} :=
  let rest :=
    match d, lpt return gtree_table with
    | 0, _ => [::]
    | d'.+1, [::] =>
      [:: gtree_merge_pairs empty_gtree_pair pt0 pt1;
          gtree_merge_pairs empty_gtree_pair empty_gtree_pair pt0]
    | d'.+1, pt :: lpt' => gtree_merge_line pt pt0 pt1 lpt' d'
    end in
  gtree_merge_pairs pt0 pt1 pt2 :: rest : gtree_table.

Fixpoint gtree_init_table d h' {struct h'} : gtree_table :=
  if h' is h''.+1 then
    let tab := gtree_init_table d.+1 h'' in
    if tab is [:: pt1, pt0 & lpt] then
      gtree_merge_line pt0 pt1 empty_gtree_pair lpt d
    else tab
  else init_gtree_h1.

Definition gtree_init_tree h :=
  match h, gtree_init_table 0 h.-1 with
  | _.+1, GtreePair t _ :: _ => t
  | _, _ => GtreeEmpty
  end.

Definition init_gtree_spec h w :=
  (size w == h) && gram_balanced 0 false (cgram 0 false w).

Lemma match_count_balanced h et :
  match_count (init_gtree_spec h) Bstack0 et =
    if (size et == h) && (Color0 \notin ctrace et) then
      dyck (count_cbit1 (ctrace et))
    else 0.
Proof.
rewrite /init_gtree_spec /ctrace /dyck; pose sb : bitseq := [::].
rewrite -[Bstack0]/(stack_of_bitseq sb) -{-4}[0]/(size sb) -(add0c (sumt et)).
have c1_lb: cbit1 Color0 = odd (size sb) by [].
pose sbs := foldr addb false.
have c0_lb: cbit0 Color0 = false (+) sbs sb by [].
elim: et h {-3}Color0 sb false c0_lb c1_lb => [|e et IHet] h c lb b0.
  case: h lb => [|h] [|b lb] //=; first by rewrite addbF => <-; case: c.
  by case: c b0 (size lb) => [] [] [].
rewrite /= addcA; case: h => [|h c0lb c1lb].
  by case: e (stack_of_bitseq lb) => [] [|sb|sb] //=; rewrite ?match_count_0.
have{IHet} := IHet h (e +c c).
rewrite cbit0_addc cbit1_addc (addcC e c) {}c0lb {}c1lb /= inE eqSS.
move: (size et == h) {c}(Color0 \in _) (count_cbit1 _) => b_h bc0 i IHet.
have /= IHet0 := IHet (cbit0 e :: lb) b0.
rewrite /= 2!addbA (addbC b0) in IHet IHet0 *.
case: e in IHet IHet0 *; rewrite ?andbF //=; first exact: IHet;
  by rewrite {}IHet0 //; case: lb IHet => [_ | b lb'']; [
    case: {3}i => *; rewrite /= ?addn0
  | rewrite ?negbK 1?addbA -1?(addbC b);
    case: b => /= ->; rewrite ?negbK //; case: (b_h && ~~ bc0)].
Qed.

Fixpoint gtree_table_sub (tab : gtree_table) n {struct tab} :=
  match tab, n with
  | [::], _ => fun _ => GtreeEmpty
  | pt :: _, 0 => gtree_pair_sub pt
  | _ :: tab', n'.+1 => gtree_table_sub tab' n'
  end.
Local Notation gtsub := gtree_table_sub.

Lemma gtree_mem_init_tree h w :
  gtree_mem (gtree_init_tree h) w = init_gtree_spec h w.
Proof.
case: h => [|h /=]; first by rewrite gtree_mem_empty; case: w.
transitivity (gtree_mem (gtsub (gtree_init_table 0 h) 0 false) w).
  by case: (gtree_init_table 0 h).
rewrite /init_gtree_spec; move: 0 {-2 3}0 false w (leqnn 0) => d.
apply: (@proj2 ((d != 0) < size (gtree_init_table d h))).
elim: h d => [|h IHh] d /=.
  by split=> [| [|[|[|n]]] [] [|s1 [|s2 w]] //]; by [case s1 | case d].
case: (gtree_init_table _ h) {IHh}(IHh d.+1) => [|pt1 [|pt0 lpt]] [_ Dsub] //.
split=> [|dw bw w ledwd]; first by case: d lpt {Dsub} => [|[|d]] [].
transitivity
  (gtree_mem (let elt := [:: empty_gtree_pair, pt1, pt0 & lpt] in
              GtreeNode (gtsub elt dw.+2 bw) (gtsub elt dw.+1 (~~ bw))
                         (gtsub elt dw bw)    (gtsub elt dw (~~ bw)))
             w).
  elim: dw d ledwd pt0 pt1 empty_gtree_pair lpt {Dsub}.
    by case: bw => [] [|d] _ [t0 t0'] [t1 t1'] [t2 t3].
  move=> dw IHdw [|d] ledwd // pt0 pt1 pt2 [{IHdw ledwd}|pt]; last exact: IHdw.
  case: dw => [|dw]; first by case: bw pt0 pt1 => [] [t1 t1'] [t2 t3].
  case: dw => [|dw]; first by case: bw pt0 => [] [t2 t3].
  by case: bw w => [] [|[] w]; rewrite /= ?gtree_mem_empty.
have ledwd1 := leqW ledwd.
case: w => [|[] w] //=; first 1 [exact: (Dsub dw.+1) | exact: Dsub];
  by case: dw {ledwd ledwd1}(leqW ledwd1) => [|dw]; last exact: Dsub;
     case: bw; rewrite andbF /= gtree_mem_empty.
Qed.

End InitialGtree.
