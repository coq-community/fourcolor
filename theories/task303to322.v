(* (c) Copyright 2006-2018 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrnat seq.
From fourcolor
Require Import cfmap cfreducible configurations.
From fourcolor
Require Import job303to306 job307to310 job311to314 job315to318 job319to322.

(******************************************************************************)
(* Reducibility of configurations number 303 to 322, whose indices in         *)
(* the_configs range over segment [302, 322).                                 *)
(******************************************************************************)

Lemma red302to322 : reducible_in_range 302 322 the_configs.
Proof.
CatReducible red302to306 red306to310 red310to314 red314to318 red318to322.
Qed.
