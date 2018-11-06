(* (c) Copyright 2006-2018 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrnat seq.
From fourcolor
Require Import cfmap cfreducible configurations.
From fourcolor
Require Import job323to383 job384to398 job399to438 job439to465 job466to485.

(******************************************************************************)
(* Reducibility of configurations number 323 to 485, whose indices in         *)
(* the_configs range over segment [322, 485).                                 *)
(******************************************************************************)

Lemma red322to485 : reducible_in_range 322 485 the_configs.
Proof.
CatReducible red322to383 red383to398 red398to438 red438to465 red465to485.
Qed.
