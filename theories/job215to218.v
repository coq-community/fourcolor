(* (c) Copyright 2006-2018 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrnat seq.
From fourcolor
Require Import cfmap cfreducible configurations.

(******************************************************************************)
(* Reducibility of configurations number 215 to 218, whose indices in         *)
(* the_configs range over segment [214, 218).                                 *)
(******************************************************************************)

Lemma red214to218 : reducible_in_range 214 218 the_configs.
Proof. CheckReducible. Qed.
