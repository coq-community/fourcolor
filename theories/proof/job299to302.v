(* (c) Copyright 2006-2018 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq.
From fourcolor Require Import cfmap cfreducible configurations.

(******************************************************************************)
(* Reducibility of configurations number 299 to 302, whose indices in         *)
(* the_configs range over segment [298, 302).                                 *)
(******************************************************************************)

Lemma red298to302 : reducible_in_range 298 302 the_configs.
Proof. CheckReducible. Qed.
