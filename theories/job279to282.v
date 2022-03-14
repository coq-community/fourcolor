(* (c) Copyright 2006-2018 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq.
From fourcolor Require Import cfmap cfreducible configurations.

(******************************************************************************)
(* Reducibility of configurations number 279 to 282, whose indices in         *)
(* the_configs range over segment [278, 282).                                 *)
(******************************************************************************)

Lemma red278to282 : reducible_in_range 278 282 the_configs.
Proof. CheckReducible. Qed.
