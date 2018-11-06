(* (c) Copyright 2006-2018 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrnat seq.
From fourcolor
Require Import cfmap cfreducible configurations.

(******************************************************************************)
(* Reducibility of configurations number 303 to 306, whose indices in         *)
(* the_configs range over segment [302, 306).                                 *)
(******************************************************************************)

Lemma red302to306 : reducible_in_range 302 306 the_configs.
Proof. CheckReducible. Qed.
