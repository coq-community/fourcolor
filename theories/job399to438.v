(* (c) Copyright 2006-2018 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrnat seq.
From fourcolor
Require Import cfmap cfreducible configurations.

(******************************************************************************)
(* Reducibility of configurations number 399 to 438, whose indices in         *)
(* the_configs range over segment [398, 438).                                 *)
(******************************************************************************)

Lemma red398to438 : reducible_in_range 398 438 the_configs.
Proof. CheckReducible. Qed.
