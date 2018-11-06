(* (c) Copyright 2006-2018 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrnat seq.
From fourcolor
Require Import cfmap cfreducible configurations.

(******************************************************************************)
(* Reducibility of configurations number 554 to 562, whose indices in         *)
(* the_configs range over segment [553, 562).                                 *)
(******************************************************************************)

Lemma red553to562 : reducible_in_range 553 562 the_configs.
Proof. CheckReducible. Qed.
