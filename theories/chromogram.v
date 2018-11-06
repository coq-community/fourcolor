(* (c) Copyright 2006-2018 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrfun ssrbool eqtype ssrnat seq choice fintype.
From fourcolor
Require Import color.

(******************************************************************************)
(*   Chromograms are words representing congruence classes of regions with    *)
(* respect to Kempe inversions for a single edge color and color permutation. *)
(* The relevant topological information for each class consists of a set of   *)
(* non-intersecting chords linking perimeter edges, and the parity of the     *)
(* number of links for each chord. The word representation of these chords is *)
(* a Dyck word augmented with spaces (for perimeter edges that are not linked *)
(* because they are colored with the inversion color) and parities (on        *)
(* closing brackets), each chord being represented with a matching bracket    *)
(* pair.                                                                      *)
(*      chromogram := seq gram_symbol with each gram_symbol one of            *)
(*         Gskip :: no chord (edge has Color1).                               *)
(*         Gpush :: chord start (edge has Color2 or Color3).                  *)
(*         Gpop0 :: odd chord end (end edge has same color as start).         *)
(*         Gpop1 :: even chord end (start and end have different colors)      *)
(* For w : chromogram, lb : bitseq, b : bool and et : colseq, we define       *)
(*  matchg lb et w <=> et is a valid edge coloring trace that matches w in a  *)
(*                     context where there are size lb open chords (started   *)
(*                     but not ended) whose corresponding edge color parities *)
(*                     are rev lb (i.e., if lb is false :: _, then the start  *)
(*                     of last open chord had edge Color2).                   *)
(*  gram_balanced d b w <=> w is balanced in a context with d open chords and *)
(*                     has parity b (i.e., matches colorings with parity b).  *)
(*  Kempe_closed P <=> P : colseq -> Prop is closed under permutations and    *)
(*                     Kempe flips: if (P et) then et matches some chromogram *)
(*                     w in the empty context, such that P holds for all edge *)
(*                     colorings that are permutations of et or that match w. *)
(*  Kempe_coclosure P et <-> P meets all Kempe_closed predicates that hold    *)
(*                     for et.                                                *)
(* --> Being a ring trace in a planar plain cubic map is Kempe_closed; the    *)
(* relation between chromograms and graphs will be developped in kempe.v.     *)
(*   As for edge color traces, we also use partial chromograms, with the last *)
(* (redundant) symbol removed, in addition to complete ones. This is the form *)
(* actually used for the correctness proof of the reducibility check.         *)
(*     cgram d b w == the complete chromogram corresponding to w, i.e., w     *)
(*                    with its last symbol restored, in the context of a      *)
(*                    chromogram prefix with d open chords and parity b.      *)
(*       bit_stack == a simple datatype equivalent to bitseq, with            *)
(*                    constructors Bstack0, Bpush0, and Bpush1. This type     *)
(*                    coerces to bitseq.                                      *)
(* matchpg bs et w <=> the chromogram completion of w matches the trace       *)
(*                    completion of et, in the context of a prefix where the  *)
(*                    colors matching the start of open chords have parities  *)
(*                    rev (bitseq_of_stack bs), respectively.                 *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive gram_symbol := Gpush | Gskip | Gpop0 | Gpop1.

Definition eqgs s1 s2 :=
  match s1, s2 with
  | Gpush, Gpush => true
  | Gskip, Gskip => true
  | Gpop0, Gpop0 => true
  | Gpop1, Gpop1 => true
  | _, _ => false
  end.

Lemma eqgsP : Equality.axiom eqgs.
Proof. by do 2!case; constructor. Qed.

Canonical gram_symbol_eqMixin := EqMixin eqgsP.
Canonical gram_symbol_eqType := EqType gram_symbol gram_symbol_eqMixin.

Definition chromogram : predArgType := seq gram_symbol.
Canonical chromogram_eqType := [eqType of chromogram].

Fixpoint gram_balanced d b0 (w : chromogram) {struct w} :=
  match w, d with
  | [::], 0 => ~~ b0
  | Gpush :: w', _ => gram_balanced d.+1 b0 w'
  | Gskip :: w', _ => gram_balanced d (~~ b0) w'
  | Gpop0 :: w', d'.+1 => gram_balanced d' b0 w'
  | Gpop1 :: w', d'.+1 => gram_balanced d' (~~ b0) w'
  | _, _ => false
  end.

Fixpoint matchg (lb : bitseq) (et : colseq) (w : chromogram) {struct w} :=
  match w, et, lb with
  | [::], [::], [::] => true
  | s :: w', e :: et', _ =>
      match e, s, lb with
      | Color1, Gskip, _            => matchg lb et' w'
      | Color2, Gpush, _            => matchg (false :: lb) et' w'
      | Color2, Gpop0, false :: lb' => matchg lb' et' w'
      | Color2, Gpop1, true :: lb'  => matchg lb' et' w'
      | Color3, Gpush, _            => matchg (true :: lb) et' w'
      | Color3, Gpop0, true :: lb'  => matchg lb' et' w'
      | Color3, Gpop1, false :: lb' => matchg lb' et' w'
      | _, _, _ => false
      end
  | _, _, _ => false
  end.

Definition Kempe_closed (P : colseq -> Prop) :=
  forall et, P et ->
    [/\ forall g, P (permt g et)
      & exists2 w, matchg [::] et w
              & forall et', matchg [::] et' w -> P et'].

Definition Kempe_coclosure P et :=
  forall P', Kempe_closed P' -> P' et -> exists2 et', P et' & P' et'.

Lemma matchg_size et lb w : matchg lb et w -> size w = size et.
Proof.
elim: et lb w => [|e et IHet] lb [|s w] etMw //=; congr _.+1; case: s etMw.
- by case: e (IHet (cbit0 e :: lb) w).
- by case: e (IHet lb w).
- by case: e lb (IHet (behead lb) w); do 3!case=> //.
by case: e lb (IHet (behead lb) w); do 3!case=> //.
Qed.

Lemma matchg_memc0 et lb w : matchg lb et w -> (Color0 \in et) = false.
Proof.
elim: et lb w => [|e et IHet] lb [|s w] //=; case: s.
- by case: e (IHet (cbit0 e :: lb) w).
- by case: e (IHet lb w).
- by case: e lb (IHet (behead lb) w); do 3!case=> //.
by case: e lb (IHet (behead lb) w); do 3!case=> //.
Qed.

Section BalanceLemmas.

Let sumb : bitseq -> bool := foldr addb false.

Lemma matchg_balanced et w :
    matchg [::] et w ->
  cbit1 (sumt et) = false /\ gram_balanced 0 (cbit0 (sumt et)) w.
Proof.
set sb := [::]; rewrite -[cbit1 _]addFb -[cbit0 _]addFb -{3}[false]/(sumb sb).
rewrite -{1}[false]/(odd 0) -[0]/(size sb).
elim: et sb w => [|e et IHet] lb [|s w] //=; first by case: lb.
rewrite cbit0_addc cbit1_addc 2!addbA -addTb.
rewrite -(addbC (cbit0 e)) -(addbC (cbit1 e)) !addbA.
case: s {IHet}(IHet (cbit0 e :: lb) w) (IHet lb w) (IHet (behead lb) w);
  by case: e => //; case: lb => [|[|] lb] //=; rewrite ?negbK.
Qed.

Lemma balanced_inj w n1 n2 b1 b2 :
  gram_balanced n1 b1 w -> gram_balanced n2 b2 w -> n1 = n2 /\ b1 = b2.
Proof.
by elim: w n1 n2 b1 b2 => [|[|||] w IHw] [|n1] [|n2] [|] [|] //= bal1 bal2;
  case: (IHw _ _ _ _ bal1 bal2) => // /(congr1 succn)[<-].
Qed.

Lemma balanced_sumt0 w et :
  gram_balanced 0 false w -> matchg [::] et w -> sumt et = Color0.
Proof.
rewrite -(ccons_cbits (sumt et)) => balFw /matchg_balanced[-> bal0w].
by have [_ ->] := balanced_inj bal0w balFw.
Qed.

Lemma match_etrace et w : matchg [::] (etrace et) w = matchg [::] et w.
Proof.
set sb := [::]; rewrite -{2}[sb]/(map negb sb) /etrace /etrace_perm.
case (even_trace et); first by rewrite permt_id.
elim: et sb w => [|e et IHet] lb [|s w] //; first by case lb.
by case: e; case: s => //=; first [rewrite IHet | case: lb => [//|[]] /=].
Qed.

(* Algorithmic predicates, for chromogram paths. *)

Inductive bit_stack : Set :=
  | Bstack0
  | Bpush0 (bs : bit_stack)
  | Bpush1 (bs : bit_stack).

Fixpoint bitseq_of_stack (bs : bit_stack) : bitseq :=
  match bs with
  | Bstack0 => [::]
  | Bpush0 bs' => false :: bitseq_of_stack bs'
  | Bpush1 bs' => true :: bitseq_of_stack bs'
  end.

Definition stack_of_bitseq : bitseq -> bit_stack :=
  foldr (fun b => if b then Bpush1 else Bpush0) Bstack0.

Fixpoint cgram d b0 (w : chromogram) {struct w} : chromogram :=
  match w with
  | [::] =>
    [:: if d is 0 then Gskip else if b0 then Gpop1 else Gpop0]
  | s :: w' =>
    s ::  match s with
        | Gpush => cgram d.+1 b0 w'
        | Gskip => cgram d (~~ b0) w'
        | Gpop0 => cgram d.-1 b0 w'
        | Gpop1 => cgram d.-1 (~~ b0) w'
        end
  end.

Fixpoint matchpg (bs : bit_stack) (et : colseq) (w : chromogram) {struct w} :=
  match w, et with
  | [::], [::] => true
  | s :: w', e :: et' =>
      match e, s, bs with
      | Color1, Gskip, _          => matchpg bs et' w'
      | Color2, Gpush, _          => matchpg (Bpush0 bs) et' w'
      | Color2, Gpop0, Bpush0 bs' => matchpg bs' et' w'
      | Color2, Gpop1, Bpush1 bs' => matchpg bs' et' w'
      | Color3, Gpop0, Bpush1 bs' => matchpg bs' et' w'
      | Color3, Gpush, _          => matchpg (Bpush1 bs) et' w'
      | Color3, Gpop1, Bpush0 bs' => matchpg bs' et' w'
      | _, _, _ => false
      end
  | _, _ => false
  end.

Lemma matchg_cgram cw et :
  matchg [::] (ctrace et) cw -> cw = cgram 0 false (take (size cw).-1 cw).
Proof.
move=> etMcw; have [_] := matchg_balanced etMcw; rewrite sumt_ctrace /=.
case: cw etMcw 0 false => [|s w _] /=; first by case et.
elim: w s => [|s' w IHw] s d b0; first by case: s b0 d; do 3!case=> //.
by case: s => //= etMw; congr (_ :: _); apply: IHw; case: d etMw; case b0.
Qed.

Lemma matchg_pg et w : gram_balanced 0 false (cgram 0 false w) ->
  matchg [::] (ctrace et) (cgram 0 false w) = matchpg Bstack0 et w.
Proof.
set sb := [::]; rewrite -[Bstack0]/(stack_of_bitseq sb) /ctrace.
rewrite -(add0c (sumt et)) -[Color0]/(ccons (odd 0) (sumb sb)).
rewrite -(addFb (sumb sb)) -[0]/(size sb).
elim: et sb false w => [|e et IHet] lb b.
  case=> [|s w] /=; first by do 2!case: b lb => [] [|b lb] //.
  move: (size lb) => d _; rewrite addc0.
  by case: (ccons _ _) s w => // [] [] // [] //; case: lb => [|[]].
case=> [|s w]; rewrite ?rcons_cons /=.
  by case: lb => [|b' [|? ?]] // _; case: e => {IHet}//;
     case: et => //; case b; case b'.
by case: s; try (case: lb; [by [] | case=> lb /=]);
  case: e (IHet (cbit0 e :: lb)) => //= IHet0; do 1?[move/IHet | move/IHet0];
  case: (sumt et) (odd _) b (sumb lb) => [] [] [] [].
Qed.

Lemma matchpg_etrace et w :
  matchpg Bstack0 (etrace et) w = matchpg Bstack0 et w.
Proof.
rewrite /etrace /etrace_perm.
case: (even_trace et) => /=; first by rewrite permt_id.
rewrite -[Bstack0]/(stack_of_bitseq [::]) -{1}[[::]]/(map negb [::]).
elim: et [::] w => [|e et IHet] lb [|s w] //.
by case: e (IHet (cbit0 e :: lb) w); case: s => //=; case: lb => [|[]] //=.
Qed.

Lemma matchpg_size et bs w : matchpg bs et w -> size w = size et.
Proof.
elim: et bs w => [|e et IHet] bs [|s w] etMw //=; congr _.+1; case: s etMw.
- by case: e (IHet ((if cbit0 e then Bpush1 else Bpush0) bs) w).
- by case: e (IHet bs w).
- by case: e bs => [] [|bs|bs] // /IHet.
by case: e bs => [] [|bs|bs] // /IHet.
Qed.

Lemma matchpg_flip et :
  matchpg Bstack0 (permt Eperm132 et) =1 matchpg Bstack0 et.
Proof.
rewrite -[Bstack0]/(stack_of_bitseq [::]) -{1}[[::]]/(map negb [::]).
move; elim: et [::] => [|e et IHet] lb [|s w] //.
by case: e (IHet (cbit0 e :: lb) w); case: s => //=; case: lb => [|[]] //=.
Qed.

End BalanceLemmas.
