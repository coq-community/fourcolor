(* (c) Copyright 2006-2018 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq.
From fourcolor Require Import cfmap cfreducible configurations.

(******************************************************************************)
(* Reducibility of configurations number 535 to 541, whose indices in         *)
(* the_configs range over segment [534, 541).                                 *)
(******************************************************************************)

Lemma red534to541 : reducible_in_range 534 541 the_configs.
Proof. CheckReducible. Qed.
