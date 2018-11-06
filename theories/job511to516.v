(* (c) Copyright 2006-2018 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrnat seq.
From fourcolor
Require Import cfmap cfreducible configurations.

(******************************************************************************)
(* Reducibility of configurations number 511 to 516, whose indices in         *)
(* the_configs range over segment [510, 516).                                 *)
(******************************************************************************)

Lemma red510to516 : reducible_in_range 510 516 the_configs.
Proof. CheckReducible. Qed.
