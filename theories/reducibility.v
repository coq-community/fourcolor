(* (c) Copyright 2006-2018 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq.
From fourcolor Require Import cfmap cfreducible configurations present.
From fourcolor Require Import task001to214 task215to234 task235to282.
From fourcolor Require Import task283to302 task303to322 task323to485.
From fourcolor Require Import task486to506 task507to541 task542to588.
From fourcolor Require Import task589to633.

(******************************************************************************)
(*   C-reducibility of all the configurations in the_configs, collating the   *)
(* proofs by reflection in all the [job|task]MMMtoMMM.v files.                *)
(******************************************************************************)

Lemma the_reducibility : reducibility.
Proof.
rewrite /reducibility; apply cat_reducible_range with 322.
  CatReducible red000to214 red214to234 red234to282 red282to302 red302to322.
CatReducible red322to485 red485to506 red506to541 red541to588 red588to633.
Qed.
