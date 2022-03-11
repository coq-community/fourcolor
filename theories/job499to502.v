(* (c) Copyright 2006-2018 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq.
From fourcolor Require Import cfmap cfreducible configurations.

(******************************************************************************)
(* Reducibility of configurations number 499 to 502, whose indices in         *)
(* the_configs range over segment [498, 502).                                 *)
(******************************************************************************)

Lemma red498to502 : reducible_in_range 498 502 the_configs.
Proof. CheckReducible. Qed.
