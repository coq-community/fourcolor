(* (c) Copyright 2006-2018 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrbool ssrnat ssrint.
From fourcolor
Require Import part hubcap present.

(******************************************************************************)
(*   This file contains the unavoidability proof for cartwheels with a hub    *)
(* arity of 5. This proof is a reencoding of the argument that appeared in    *)
(* the main text of the Robertson et al. revised proof.                       *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma exclude5 : excluded_arity 5.
Proof.
Presentation red.
Pcase L0_1: s[1] <= 5.
  Pcase L1_1: s[2] <= 5.
    Pcase L2_1: s[3] <= 6.
      Pcase: s[3] <= 5.
        Reducible.
      Pcase: s[4] <= 5.
        Reducible.
      Pcase: s[5] > 6.
        Hubcap $[1,2]<=0 $[3,4]<=(-6) $[5]<=(-4) $.
      Pcase: s[5] > 5.
        Hubcap $[1,2]<=0 $[3,4]<=(-7) $[5]<=(-3) $.
      Reducible.
    Pcase: s[5] <= 6.
      Similar to *L2_1[3].
    Pcase: s[4] > 5.
      Hubcap $[1,2]<=0 $[3,4]<=(-6) $[5]<=(-4) $.
    Hubcap $[1,2]<=0 $[3,4]<=(-5) $[5]<=(-5) $.
  Pcase: s[5] <= 5.
    Similar to L1_1[4].
  Pcase L1_2: s[3] <= 5.
    Pcase: s[2] <= 6.
      Reducible.
    Pcase: s[4] <= 5.
      Similar to L1_1[2].
    Pcase L2_1: s[4] <= 6.
      Pcase: s[5] <= 6.
        Reducible.
      Hubcap $[1,2]<=(-4) $[3,4]<=(-2) $[5]<=(-4) $.
    Pcase: s[5] <= 6.
      Similar to *L2_1[2].
    Hubcap $[1,2]<=(-4) $[3,4]<=(-3) $[5]<=(-3) $.
  Pcase: s[4] <= 5.
    Similar to *L1_2[4].
  Pcase L1_3: s[2] > 6.
    Pcase: s[5] > 6.
      Hubcap $[1,2]<=(-3) $[3,4]<=(-4) $[5]<=(-3) $.
    Hubcap $[1,2]<=(-3) $[3,4]<=(-5) $[5]<=(-2) $.
  Pcase: s[5] > 6.
    Similar to *L1_3[4].
  Hubcap $[1,2]<=(-2) $[3,4]<=(-6) $[5]<=(-2) $.
Pcase: s[2] <= 5.
  Similar to L0_1[1].
Pcase: s[3] <= 5.
  Similar to L0_1[2].
Pcase: s[4] <= 5.
  Similar to L0_1[3].
Pcase: s[5] <= 5.
  Similar to L0_1[4].
Hubcap $[1,2]<=(-4) $[3,4]<=(-4) $[5]<=(-2) $.
Qed.
