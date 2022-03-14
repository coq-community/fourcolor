(* (c) Copyright 2006-2018 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq.
From fourcolor Require Import cfmap cfreducible configurations.

(******************************************************************************)
(* Reducibility of configurations number 107 to 164, whose indices in         *)
(* the_configs range over segment [106, 164).                                 *)
(******************************************************************************)

Lemma red106to164 : reducible_in_range 106 164 the_configs.
Proof. CheckReducible. Qed.
