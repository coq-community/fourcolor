(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrnat seq.
From fourcolor
Require Import cfmap cfreducible configurations.
From fourcolor
Require Import job486to489 job490to494 job495to498 job499to502 job503to506.

(******************************************************************************)
(* Reducibility of configurations number 486 to 506, whose indices in         *)
(* the_configs range over segment [485, 506).                                 *)
(******************************************************************************)

Lemma red485to506 : reducible_in_range 485 506 the_configs.
Proof.
CatReducible red485to489 red489to494 red494to498 red498to502 red502to506.
Qed.
