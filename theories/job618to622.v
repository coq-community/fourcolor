(* (c) Copyright 2006-2018 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrnat seq.
From fourcolor
Require Import cfmap cfreducible configurations.

(******************************************************************************)
(* Reducibility of configurations number 618 to 622, whose indices in         *)
(* the_configs range over segment [617, 622).                                 *)
(******************************************************************************)

Lemma red617to622 : reducible_in_range 617 622 the_configs.
Proof. CheckReducible. Qed.
