(* (c) Copyright 2006-2018 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrnat seq.
From fourcolor
Require Import cfmap cfreducible configurations.

(******************************************************************************)
(* Reducibility of configurations number 223 to 226, whose indices in         *)
(* the_configs range over segment [222, 226).                                 *)
(******************************************************************************)

Lemma red222to226 : reducible_in_range 222 226 the_configs.
Proof. CheckReducible. Qed.
