(* (c) Copyright 2006-2018 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq.
From fourcolor Require Import cfmap cfreducible configurations.

(******************************************************************************)
(* Reducibility of configurations number 283 to 286, whose indices in         *)
(* the_configs range over segment [282, 286).                                 *)
(******************************************************************************)

Lemma red282to286 : reducible_in_range 282 286 the_configs.
Proof. CheckReducible. Qed.
