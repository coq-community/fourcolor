(* (c) Copyright 2006-2018 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrnat seq.
From fourcolor
Require Import cfmap cfreducible configurations.

(******************************************************************************)
(* Reducibility of configurations number 531 to 534, whose indices in         *)
(* the_configs range over segment [530, 534).                                 *)
(******************************************************************************)

Lemma red530to534 : reducible_in_range 530 534 the_configs.
Proof. CheckReducible. Qed.
