(* (c) Copyright 2006-2018 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrnat seq.
From fourcolor
Require Import cfmap cfreducible configurations.

(******************************************************************************)
(* Reducibility of configurations number 490 to 494, whose indices in         *)
(* the_configs range over segment [489, 494).                                 *)
(******************************************************************************)

Lemma red489to494 : reducible_in_range 489 494 the_configs.
Proof. CheckReducible. Qed.
