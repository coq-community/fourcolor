(* (c) Copyright 2006-2018 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import fintype path fingraph ssralg ssrnum ssrint.
From fourcolor Require Import hypermap geometry coloring patch birkhoff part.
From fourcolor Require Import discharge configurations hubcap present.
From fourcolor Require Import present5 present6 present7 present8 present9.
From fourcolor Require Import present10 present11.

(******************************************************************************)
(*   The main unavoidability theorem: reducibility implies no minimal counter *)
(* example, collating the result of all the presentNN.v files.                *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma unavoidability : reducibility -> forall G, ~ minimal_counter_example G.
Proof.
move=> red_check G cexG; have [x pos_x] := posz_dscore cexG.
suffices: arity x \in iota 5 7.
  rewrite !inE exclude5 ?exclude6 ?exclude7 ?exclude8 //=.
  by rewrite exclude9 ?exclude10 ?exclude11.
rewrite mem_iota (cexG : pentagonal G) (@dscore_cap1 G 5) {x pos_x}// => y.
have{y} [x ->]: {x | y = face (face x)} by exists (inv_face2 y); rewrite !nodeK.
pose n := arity x; pose rf := DruleFork (DruleForkValues n).
rewrite (dbound1_eq rf) // lez_nat.
have [Dn | /source_drules_range-> //] := boolP (Pr58 n).
have fit_x: exact_fitp x (pcons_ n) by apply: exact_fitp_pcons_ cexG _.
apply: (check_dbound1P (no_fit_the_redpart red_check cexG)) fit_x _ => //.
by case/or4P: Dn @rf => /eqP->.
Qed.
