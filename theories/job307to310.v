(* (c) Copyright 2006-2018 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrnat seq.
From fourcolor
Require Import cfmap cfreducible configurations.

(******************************************************************************)
(* Reducibility of configurations number 307 to 310, whose indices in         *)
(* the_configs range over segment [306, 310).                                 *)
(******************************************************************************)

Lemma red306to310 : reducible_in_range 306 310 the_configs.
Proof. CheckReducible. Qed.
