(* (c) Copyright 2006-2018 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrnat seq.
From fourcolor
Require Import cfmap cfreducible configurations.

(******************************************************************************)
(* Reducibility of configurations number 254 to 270, whose indices in         *)
(* the_configs range over segment [253, 270).                                 *)
(******************************************************************************)

Lemma red253to270 : reducible_in_range 253 270 the_configs.
Proof. CheckReducible. Qed.
