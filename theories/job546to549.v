(* (c) Copyright 2006-2018 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq.
From fourcolor Require Import cfmap cfreducible configurations.

(******************************************************************************)
(* Reducibility of configurations number 546 to 549, whose indices in         *)
(* the_configs range over segment [545, 549).                                 *)
(******************************************************************************)

Lemma red545to549 : reducible_in_range 545 549 the_configs.
Proof. CheckReducible. Qed.
