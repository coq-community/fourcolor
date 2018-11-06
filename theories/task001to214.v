(* (c) Copyright 2006-2018 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrnat seq.
From fourcolor
Require Import cfmap cfreducible configurations.
From fourcolor
Require Import job001to106 job107to164 job165to189 job190to206 job207to214.

(******************************************************************************)
(* Reducibility of configurations number 1 to 214, whose indices in           *)
(* the_configs range over segment [0, 214).                                   *)
(******************************************************************************)

Lemma red000to214 : reducible_in_range 0 214 the_configs.
Proof.
CatReducible red000to106 red106to164 red164to189 red189to206 red206to214.
Qed.
