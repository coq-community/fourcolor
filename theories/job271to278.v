(* (c) Copyright 2006-2018 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrnat seq.
From fourcolor
Require Import cfmap cfreducible configurations.

(******************************************************************************)
(* Reducibility of configurations number 271 to 278, whose indices in         *)
(* the_configs range over segment [270, 278).                                 *)
(******************************************************************************)

Lemma red270to278 : reducible_in_range 270 278 the_configs.
Proof. CheckReducible. Qed.
