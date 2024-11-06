(* (c) Copyright 2006-2018 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq.
From fourcolor Require Import cfmap cfreducible configurations.

(******************************************************************************)
(* Reducibility of configurations number 231 to 234, whose indices in         *)
(* the_configs range over segment [230, 234).                                 *)
(******************************************************************************)

Lemma red230to234 : reducible_in_range 230 234 the_configs.
Proof. CheckReducible. Qed.
