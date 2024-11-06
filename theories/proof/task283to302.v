(* (c) Copyright 2006-2018 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq.
From fourcolor Require Import cfmap cfreducible configurations.
From fourcolor Require Import job283to286 job287to290 job291to294.
From fourcolor Require Import job295to298 job299to302.

(******************************************************************************)
(* Reducibility of configurations number 283 to 302, whose indices in         *)
(* the_configs range over segment [282, 302).                                 *)
(******************************************************************************)

Lemma red282to302 : reducible_in_range 282 302 the_configs.
Proof.
CatReducible red282to286 red286to290 red290to294 red294to298 red298to302.
Qed.
