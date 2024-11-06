(* (c) Copyright 2006-2018 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq.
From fourcolor Require Import cfmap cfreducible configurations.

(******************************************************************************)
(* Reducibility of configurations number 319 to 322, whose indices in         *)
(* the_configs range over segment [318, 322).                                 *)
(******************************************************************************)

Lemma red318to322 : reducible_in_range 318 322 the_configs.
Proof. CheckReducible. Qed.
