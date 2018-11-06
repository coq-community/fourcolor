(* (c) Copyright 2006-2018 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrnat seq.
From fourcolor
Require Import cfmap cfreducible configurations.

(******************************************************************************)
(* Reducibility of configurations number 291 to 294, whose indices in         *)
(* the_configs range over segment [290, 294).                                 *)
(******************************************************************************)

Lemma red290to294 : reducible_in_range 290 294 the_configs.
Proof. CheckReducible. Qed.
