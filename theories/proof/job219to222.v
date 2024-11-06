(* (c) Copyright 2006-2018 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq.
From fourcolor Require Import cfmap cfreducible configurations.

(******************************************************************************)
(* Reducibility of configurations number 219 to 222, whose indices in         *)
(* the_configs range over segment [218, 222).                                 *)
(******************************************************************************)

Lemma red218to222 : reducible_in_range 218 222 the_configs.
Proof. CheckReducible. Qed.
