(* (c) Copyright 2006-2018 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq.
From fourcolor Require Import cfmap cfreducible configurations.

(******************************************************************************)
(* Reducibility of configurations number 235 to 238, whose indices in         *)
(* the_configs range over segment [234, 238).                                 *)
(******************************************************************************)

Lemma red234to238 : reducible_in_range 234 238 the_configs.
Proof. CheckReducible. Qed.
