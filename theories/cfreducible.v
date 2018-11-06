(* (c) Copyright 2006-2018 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrfun ssrbool eqtype ssrnat seq choice fintype path fingraph.
From fourcolor
Require Import hypermap geometry color chromogram coloring kempe.
From fourcolor
Require Import cfmap cfcolor cfcontract ctree kempetree.

(******************************************************************************)
(*   The reducibility decision procedure; we only use C-reductibility, as the *)
(* source data for D-reducible configurations has been completed with an      *)
(* arbitrary contraction.                                                     *)
(*  Definitions:                                                              *)
(*    check_reducible cf <=> cf : config passes the C-reducibility check,     *)
(*                           with a well-formed cprog and valid contract:     *)
(*                           contract_ctree cf returns a ctree disjoint from  *)
(*                           the ctree of the Kempe co-closure of the         *)
(*                           colorings of cfmap cf.                           *)
(*        cfreducible cf <-> cfmap cf is semantically C-reducible with        *)
(*                           contract cfcontract cf.                          *)
(*  reducible_in_range i j cfs <-> all configurations in the range [i, j) in  *)
(*                           cfs : seq_config pass the check_reducible test.  *)
(*        CheckReducible :: tactic using computational reflection to prove a  *)
(*                           reducible_in_range i j cfs subgoal.              *)
(*  CatReducible lem1 .. lem5 :: tactic for proving a reducible_in_range i j  *)
(*                           subgoal by combining proofs lem[1-5] of          *)
(*                           reducible_in_range for five contiguous subranges *)
(*                           covering [i, j).                                 *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section CfReducible.

Variable cf : config.

Definition check_reducible :=
  oapp (ctree_disjoint (Kempe_tree (cfprog cf))) false (contract_ctree cf).

Definition cfreducible := C_reducible (cfring cf) (cfcontract cf).

Lemma check_reducible_valid : check_reducible -> cfreducible.
Proof.
rewrite /check_reducible /cfreducible; have:= contract_ctreeP cf.
move: (cfcontract cf) (contract_ctree cf) => cc [] // cct [cc_ok cc_col] cc'K.
split=> // et tr_et; have [k _ Det] := tr_et.
have Eet: size (behead et) = (cprsize (cfprog cf)).-1.
  by rewrite size_behead Det size_trace size_map /cfring revK -size_ring_cpmap.
have{cc'K cc_col tr_et} := ctree_mem_disjoint cc'K (cc_col et tr_et).
move/(Kempe_treeP Eet){Eet}; rewrite -/(cfmap cf).
have {k Det} <-: rot 1 et = ctrace (behead et).
  have: sumt et == Color0 by apply/eqP; rewrite Det; apply: sumt_trace.
  case: et Det => [|e et' _] /=.
    by rewrite revK head_cpring /= [ctrace _]headI.
  by rewrite rot1_cons /ctrace addc_eq0 => /eqP->.
move=> IHet  P closedP Pet; pose P1 (et1 : colseq) := P (rotr 1 et1).
have{closedP} closedP1: Kempe_closed P1.
  move=> et1 /closedP[P1et1g [w et1Mw wPet1]].
  split=> [h|]; first by rewrite /P1 -map_rotr; apply: P1et1g.
  exists (gram_rot w)=> [|et2]; first by rewrite -(rotrK 1 et1) match_gram_rot.
  by rewrite -{1}(rotrK 1 et2) match_gram_rot; apply: wPet1.
rewrite -(rotK 1 et) in Pet.
have{et IHet closedP1 Pet} [et [k col_k Det] P1et] := IHet _ closedP1 Pet.
exists (rotr 1 et) => //; exists k => //.
by rewrite revK Det map_rot trace_rot rotK.
Qed.

End CfReducible.

(* This predicate hides the (expensive) reducibility evaluation. *)

Section IndexConfig.

Import ConfigSyntax.

Definition cf000 := Config 0 H.

End IndexConfig.

Definition reducible_in_range j1 j2 (cfs : seq config) :=
  forall i, j1 <= i -> i < j2 -> cfreducible (nth cf000 cfs i).

Lemma check_reducible_in_range j1 j2 (cfs : seq config) :
    (forall i, let n := j2 - j1 in
    n <= i \/ check_reducible (nth cf000 (take n (drop j1 cfs)) i)) ->
  reducible_in_range j1 j2 cfs.
Proof.
move=> red_j12 i j1_le_i i_lt_j2; set n := j2 - j1; set i' := i - j1.
have le_j12: j1 <= j2 by apply ltnW; apply: leq_trans i_lt_j2.
have i'_lt_n: i' < n by rewrite -subSn // leq_subLR subnKC.
case: {red_j12}(red_j12 i'); rewrite -/n; first by rewrite leqNgt i'_lt_n.
by rewrite nth_take // nth_drop subnKC //; apply: check_reducible_valid.
Qed.

Ltac CheckReducible :=
  apply check_reducible_in_range => /=;
  do ![case; [right; exact <: isT | try by left]]. 

Lemma cat_reducible_range j1 j2 cfs :
   reducible_in_range j1 j2 cfs ->
  forall j3, reducible_in_range j2 j3 cfs -> reducible_in_range j1 j3 cfs.
Proof.
move=> red_12 j3 red_j23 i j1_le_i i_lt_j3.
by case: (ltnP i j2) => [/red_12 | /red_j23]; apply.
Qed.

Ltac CatReducible h1 h2 h3 h4 h5 :=
  apply (cat_reducible_range h1); apply (cat_reducible_range h2);
  apply (cat_reducible_range h3); apply (cat_reducible_range h4);
  exact h5.


