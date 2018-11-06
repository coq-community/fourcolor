(* (c) Copyright 2006-2018 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrnat seq.
From fourcolor
Require Import cfmap cfreducible configurations.

(******************************************************************************)
(* Reducibility of configurations number 239 to 253, whose indices in         *)
(* the_configs range over segment [238, 253).                                 *)
(******************************************************************************)

Lemma red238to253 : reducible_in_range 238 253 the_configs.
Proof. CheckReducible. Qed.
