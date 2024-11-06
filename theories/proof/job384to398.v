(* (c) Copyright 2006-2018 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq.
From fourcolor Require Import cfmap cfreducible configurations.

(******************************************************************************)
(* Reducibility of configurations number 384 to 398, whose indices in         *)
(* the_configs range over segment [383, 398).                                 *)
(******************************************************************************)

Lemma red383to398 : reducible_in_range 383 398 the_configs.
Proof. CheckReducible. Qed.
