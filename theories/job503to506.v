(* (c) Copyright 2006-2018 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq.
From fourcolor Require Import cfmap cfreducible configurations.

(******************************************************************************)
(* Reducibility of configurations number 503 to 506, whose indices in         *)
(* the_configs range over segment [502, 506).                                 *)
(******************************************************************************)

Lemma red502to506 : reducible_in_range 502 506 the_configs.
Proof. CheckReducible. Qed.
