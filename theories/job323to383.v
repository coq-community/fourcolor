(* (c) Copyright 2006-2018 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrnat seq.
From fourcolor
Require Import cfmap cfreducible configurations.

(******************************************************************************)
(* Reducibility of configurations number 323 to 383, whose indices in         *)
(* the_configs range over segment [322, 383).                                 *)
(******************************************************************************)

Lemma red322to383 : reducible_in_range 322 383 the_configs.
Proof. CheckReducible. Qed.
