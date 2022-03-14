(* (c) Copyright 2006-2018 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq.
From fourcolor Require Import cfmap cfreducible configurations.

(******************************************************************************)
(* Reducibility of configurations number 611 to 617, whose indices in         *)
(* the_configs range over segment [610, 617).                                 *)
(******************************************************************************)

Lemma red610to617 : reducible_in_range 610 617 the_configs.
Proof. CheckReducible. Qed.
