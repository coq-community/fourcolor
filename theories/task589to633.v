(* (c) Copyright 2006-2018 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrnat seq.
From fourcolor
Require Import cfmap cfreducible configurations.
From fourcolor
Require Import job589to610 job611to617 job618to622 job623to633.

(******************************************************************************)
(* Reducibility of configurations number 589 to 633, whose indices in         *)
(* the_configs range over segment [588, 633). It's the end of that list.      *)
(******************************************************************************)

Lemma red588to633 : reducible_in_range 588 633 the_configs.
Proof.
have red633: reducible_in_range 633 633 the_configs.
  by apply check_reducible_in_range; left.
CatReducible red588to610 red610to617 red617to622 red622to633 red633.
Qed.
