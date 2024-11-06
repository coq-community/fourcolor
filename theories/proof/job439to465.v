(* (c) Copyright 2006-2018 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq.
From fourcolor Require Import cfmap cfreducible configurations.

(******************************************************************************)
(* Reducibility of configurations number 439 to 465, whose indices in         *)
(* the_configs range over segment [438, 465).                                 *)
(******************************************************************************)

Lemma red438to465 : reducible_in_range 438 465 the_configs.
Proof. CheckReducible. Qed.
