(* (c) Copyright 2006-2018 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq.
From fourcolor Require Import cfmap cfreducible configurations.

(******************************************************************************)
(* Reducibility of configurations number 190 to 206, whose indices in         *)
(* the_configs range over segment [189, 206).                                 *)
(******************************************************************************)

Lemma red189to206 : reducible_in_range 189 206 the_configs.
Proof. CheckReducible. Qed.
