(* (c) Copyright 2006-2018 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrnat seq.
From fourcolor
Require Import cfmap cfreducible configurations.
From fourcolor
Require Import job507to510 job511to516 job517to530 job531to534 job535to541.

(******************************************************************************)
(* Reducibility of configurations number 507 to 541, whose indices in         *)
(* the_configs range over segment [506, 541).                                 *)
(******************************************************************************)

Lemma red506to541 : reducible_in_range 506 541 the_configs.
Proof.
CatReducible red506to510 red510to516 red516to530 red530to534 red534to541.
Qed.
