(* (c) Copyright 2006-2018 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq.
From fourcolor Require Import cfmap cfreducible configurations.

(******************************************************************************)
(* Reducibility of configurations number 507 to 510, whose indices in         *)
(* the_configs range over segment [506, 510).                                 *)
(******************************************************************************)

Lemma red506to510 : reducible_in_range 506 510 the_configs.
Proof. CheckReducible. Qed.
