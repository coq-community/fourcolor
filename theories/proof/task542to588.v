(* (c) Copyright 2006-2018 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq.
From fourcolor Require Import cfmap cfreducible configurations.
From fourcolor Require Import job542to545 job546to549 job550to553.
From fourcolor Require Import job554to562 job563to588.

(******************************************************************************)
(* Reducibility of configurations number 542 to 588, whose indices in         *)
(* the_configs range over segment [541, 588).                                 *)
(******************************************************************************)

Lemma red541to588 : reducible_in_range 541 588 the_configs.
Proof.
CatReducible red541to545 red545to549 red549to553 red553to562 red562to588.
Qed.
