(* (c) Copyright 2006-2018 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrnat seq.
From fourcolor
Require Import cfmap cfreducible configurations.

(******************************************************************************)
(* Reducibility of configurations number 1 to 106, whose indices in           *)
(* the_configs range over segment [0, 106).                                   *)
(******************************************************************************)

Lemma red000to106 : reducible_in_range 0 106 the_configs.
Proof. CheckReducible. Qed.
