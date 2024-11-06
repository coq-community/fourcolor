(* (c) Copyright 2006-2018 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq.
From fourcolor Require Import cfmap cfreducible configurations.

(******************************************************************************)
(* Reducibility of configurations number 287 to 290, whose indices in         *)
(* the_configs range over segment [286, 290).                                 *)
(******************************************************************************)

Lemma red286to290 : reducible_in_range 286 290 the_configs.
Proof. CheckReducible. Qed.
