(* (c) Copyright 2006-2018 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq.
From fourcolor Require Import cfmap cfreducible configurations.

(******************************************************************************)
(* Reducibility of configurations number 623 to 633, whose indices in         *)
(* the_configs range over segment [622, 633); it's end of the list.           *)
(******************************************************************************)

Lemma red622to633 : reducible_in_range 622 633 the_configs.
Proof. CheckReducible. Qed.
