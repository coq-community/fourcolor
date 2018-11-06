(* (c) Copyright 2006-2018 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrnat seq.
From fourcolor
Require Import cfmap cfreducible configurations.

(******************************************************************************)
(* Reducibility of configurations number 542 to 545, whose indices in         *)
(* the_configs range over segment [541, 545).                                 *)
(******************************************************************************)

Lemma red541to545 : reducible_in_range 541 545 the_configs.
Proof. CheckReducible. Qed.
