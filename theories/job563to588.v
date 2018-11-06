(* (c) Copyright 2006-2018 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrnat seq.
From fourcolor
Require Import cfmap cfreducible configurations.

(******************************************************************************)
(* Reducibility of configurations number 563 to 588, whose indices in         *)
(* the_configs range over segment [562, 588).                                 *)
(******************************************************************************)

Lemma red562to588 : reducible_in_range 562 588 the_configs.
Proof. CheckReducible. Qed.
