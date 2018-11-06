(* (c) Copyright 2006-2018 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrnat seq.
From fourcolor
Require Import cfmap cfreducible configurations.

(******************************************************************************)
(* Reducibility of configurations number 165 to 189, whose indices in         *)
(* the_configs range over segment [164, 189).                                 *)
(******************************************************************************)

Lemma red164to189 : reducible_in_range 164 189 the_configs.
Proof. CheckReducible. Qed.
