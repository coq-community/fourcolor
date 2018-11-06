(* (c) Copyright 2006-2018 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrnat seq.
From fourcolor
Require Import cfmap cfreducible configurations.

(******************************************************************************)
(* Reducibility of configurations number 207 to 214, whose indices in         *)
(* the_configs range over segment [206, 214).                                 *)
(******************************************************************************)

Lemma red206to214 : reducible_in_range 206 214 the_configs.
Proof. CheckReducible. Qed.
