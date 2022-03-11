(* (c) Copyright 2006-2018 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq.
From fourcolor Require Import cfmap cfreducible configurations.

(******************************************************************************)
(* Reducibility of configurations number 495 to 498, whose indices in         *)
(* the_configs range over segment [494, 498).                                 *)
(******************************************************************************)

Lemma red494to498 : reducible_in_range 494 498 the_configs.
Proof. CheckReducible. Qed.
