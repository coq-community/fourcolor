(* (c) Copyright 2006-2018 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrnat seq.
From fourcolor
Require Import cfmap cfreducible configurations.
From fourcolor
Require Import job235to238 job239to253 job254to270 job271to278 job279to282.

(******************************************************************************)
(* Reducibility of configurations number 235 to 282, whose indices in         *)
(* the_configs range over segment [234, 282).                                 *)
(******************************************************************************)

Lemma red234to282 : reducible_in_range 234 282 the_configs.
Proof.
CatReducible red234to238 red238to253 red253to270 red270to278 red278to282.
Qed.
