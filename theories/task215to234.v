(* (c) Copyright 2006-2018 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrnat seq.
From fourcolor
Require Import cfmap cfreducible configurations.
From fourcolor
Require Import job215to218 job219to222 job223to226 job227to230 job231to234.

(******************************************************************************)
(* Reducibility of configurations number 215 to 234, whose indices in         *)
(* the_configs range over segment [214, 234).                                 *)
(******************************************************************************)

Lemma red214to234 : reducible_in_range 214 234 the_configs.
Proof.
CatReducible red214to218 red218to222 red222to226 red226to230 red230to234.
Qed.
