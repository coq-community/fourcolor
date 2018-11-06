(* (c) Copyright 2006-2018 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrnat seq.
From fourcolor
Require Import cfmap cfreducible configurations.

(******************************************************************************)
(* Reducibility of configurations number 486 to 489, whose indices in         *)
(* the_configs range over segment [485, 489).                                 *)
(******************************************************************************)

Lemma red485to489 : reducible_in_range 485 489 the_configs.
Proof. CheckReducible. Qed.
