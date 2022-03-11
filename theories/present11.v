(* (c) Copyright 2006-2018 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssrint.
From fourcolor Require Import part hubcap present.

(******************************************************************************)
(*   This file contains the unavoidability proof for cartwheels with a hub    *)
(* arity of 11. This proof is distilled from the supporting data for the      *)
(* Robertson et al. revised proof.                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma exclude11 : excluded_arity 11.
Proof.
Presentation red.
Pcase L0_1: s[1] > 7.
  Hubcap $[1]<=2 $[2]<=4 $[3]<=5 $[4]<=5 $[5]<=5 $[6]<=5 $[7]<=5 $[8]<=5 $[9]<=5
         $[10]<=5 $[11]<=4 $.
Pcase: s[2] > 7.
  Similar to L0_1[1].
Pcase: s[3] > 7.
  Similar to L0_1[2].
Pcase: s[4] > 7.
  Similar to L0_1[3].
Pcase: s[5] > 7.
  Similar to L0_1[4].
Pcase: s[6] > 7.
  Similar to L0_1[5].
Pcase: s[7] > 7.
  Similar to L0_1[6].
Pcase: s[8] > 7.
  Similar to L0_1[7].
Pcase: s[9] > 7.
  Similar to L0_1[8].
Pcase: s[10] > 7.
  Similar to L0_1[9].
Pcase: s[11] > 7.
  Similar to L0_1[10].
Pcase L0_2: s[1] > 6.
  Pcase L1_1: s[2] > 5.
    Hubcap $[1]<=4 $[2]<=3 $[3]<=4 $[4]<=5 $[5]<=5 $[6]<=5 $[7]<=5 $[8]<=5
           $[9]<=5 $[10]<=5 $[11]<=4 $.
  Pcase: s[11] > 5.
    Similar to *L1_1[10].
  Pcase L1_2: s[3] > 6.
    Pcase: s[4] > 5.
      Similar to L1_1[2].
    Hubcap $[1]<=4 $[2]<=2 $[3]<=4 $[4]<=4 $[5]<=5 $[6]<=5 $[7]<=5 $[8]<=5
           $[9]<=5 $[10]<=5 $[11]<=4 $.
  Pcase: s[10] > 6.
    Similar to L1_2[9].
  Pcase L1_3: s[4] > 6.
    Pcase: s[3] > 5.
      Similar to *L1_1[7].
    Pcase: s[5] > 5.
      Similar to L1_1[3].
    Pcase: s[6] > 6.
      Similar to L1_2[3].
    Hubcap $[1]<=4 $[2]<=4 $[3]<=4 $[4]<=4 $[5]<=4 $[6]<=5 $[7]<=5 $[8]<=5
           $[9]<=5 $[10]<=5 $[11]<=4 $.
  Pcase: s[9] > 6.
    Similar to L1_3[8].
  Pcase L1_4: s[5] > 6.
    Pcase: s[4] > 5.
      Similar to *L1_1[6].
    Pcase: s[6] > 5.
      Similar to L1_1[4].
    Pcase: s[7] > 6.
      Similar to L1_2[4].
    Pcase: s[8] > 6.
      Similar to L1_3[4].
    Hubcap $[1]<=4 $[2]<=4 $[3]<=5 $[4]<=4 $[5]<=4 $[6]<=4 $[7]<=5 $[8]<=5
           $[9]<=5 $[10]<=5 $[11]<=4 $.
  Pcase: s[8] > 6.
    Similar to L1_4[7].
  Pcase L1_5: s[6] > 6.
    Pcase: s[5] > 5.
      Similar to *L1_1[5].
    Pcase: s[7] > 5.
      Similar to L1_1[5].
    Hubcap $[1]<=4 $[2]<=4 $[3]<=5 $[4]<=5 $[5]<=4 $[6]<=4 $[7]<=4 $[8]<=5
           $[9]<=5 $[10]<=5 $[11]<=4 $.
  Pcase: s[7] > 6.
    Similar to L1_5[6].
  Pcase: s[3] > 5.
    Hubcap $[1]<=4 $[2]<=3 $[3]<=5 $[6]<=5 $[7]<=5 $[8]<=5 $[9]<=5 $[10]<=5
           $[11]<=4 $[4,5]<=9 $.
  Pcase: s[4] > 5.
    Hubcap $[1]<=4 $[2]<=4 $[3]<=4 $[4]<=5 $[7]<=5 $[8]<=5 $[9]<=5 $[10]<=5
           $[11]<=4 $[5,6]<=9 $.
  Pcase: s[5] > 5.
    Hubcap $[1]<=4 $[2]<=4 $[3]<=5 $[4]<=4 $[5]<=5 $[8]<=5 $[9]<=5 $[10]<=5
           $[11]<=4 $[6,7]<=9 $.
  Pcase: s[6] > 5.
    Hubcap $[1]<=4 $[2]<=4 $[3]<=5 $[4]<=5 $[5]<=4 $[6]<=5 $[9]<=5 $[10]<=5
           $[11]<=4 $[7,8]<=9 $.
  Pcase: s[7] > 5.
    Hubcap $[1]<=4 $[2]<=4 $[3]<=5 $[4]<=5 $[5]<=5 $[6]<=4 $[7]<=5 $[10]<=5
           $[11]<=4 $[8,9]<=9 $.
  Hubcap $[1]<=4 $[2]<=4 $[3]<=5 $[4]<=5 $[5]<=5 $[6]<=5 $[11]<=4 $[7,8]<=9
         $[9,10]<=9 $.
Pcase: s[2] > 6.
  Similar to L0_2[1].
Pcase: s[3] > 6.
  Similar to L0_2[2].
Pcase: s[4] > 6.
  Similar to L0_2[3].
Pcase: s[5] > 6.
  Similar to L0_2[4].
Pcase: s[6] > 6.
  Similar to L0_2[5].
Pcase: s[7] > 6.
  Similar to L0_2[6].
Pcase: s[8] > 6.
  Similar to L0_2[7].
Pcase: s[9] > 6.
  Similar to L0_2[8].
Pcase: s[10] > 6.
  Similar to L0_2[9].
Pcase: s[11] > 6.
  Similar to L0_2[10].
Pcase L0_3: s[1] > 5.
  Pcase L1_1: s[2] > 5.
    Pcase: s[3] > 5.
      Hubcap $[1]<=4 $[2]<=4 $[3]<=4 $[4]<=4 $[5]<=5 $[6]<=5 $[7]<=5 $[8]<=5
             $[9]<=5 $[10]<=5 $[11]<=4 $.
    Pcase: s[4] > 5.
      Hubcap $[3]<=4 $[4]<=5 $[7]<=5 $[8]<=5 $[9]<=5 $[10]<=5 $[11]<=4 $[1,2]<=8
             $[5,6]<=9 $.
    Pcase: s[5] > 5.
      Hubcap $[3]<=4 $[4]<=4 $[5]<=5 $[6]<=5 $[7]<=5 $[8]<=5 $[9]<=5 $[10]<=5
             $[11]<=4 $[1,2]<=8 $.
    Pcase: s[6] > 5.
      Hubcap $[3]<=4 $[4]<=5 $[5]<=4 $[6]<=5 $[7]<=5 $[8]<=5 $[9]<=5 $[10]<=5
             $[11]<=4 $[1,2]<=8 $.
    Hubcap $[3]<=4 $[4]<=5 $[5]<=5 $[6]<=5 $[7]<=5 $[10]<=5 $[11]<=4 $[1,2]<=8
           $[8,9]<=9 $.
  Pcase: s[11] > 5.
    Similar to L1_1[10].
  Pcase L1_2: s[3] <= 5.
    Pcase L2_1: s[4] <= 5.
      Pcase L3_1: s[5] <= 5.
        Pcase L4_1: s[6] <= 5.
          Pcase: s[7] <= 5.
            Pcase: s[8] <= 5.
              Pcase: s[9] <= 5.
                Reducible.
              Pcase: s[10] > 5.
                Similar to L1_1[8].
              Pcase: h[2] > 6.
                Hubcap $[1]<=4 $[2]<=4 $[3]<=5 $[4]<=5 $[5]<=5 $[6]<=5 $[7]<=5
                       $[8]<=4 $[9]<=5 $[10]<=4 $[11]<=4 $.
              Pcase: f1[1] <= 5.
                Reducible.
              Pcase: h[9] > 6.
                Hubcap $[1]<=5 $[2]<=4 $[3]<=5 $[4]<=5 $[5]<=5 $[6]<=5 $[7]<=5
                       $[8]<=4 $[9]<=4 $[10]<=4 $[11]<=4 $.
              Pcase: f1[9] <= 5.
                Reducible.
              Pcase: h[10] > 6.
                Hubcap $[1]<=5 $[2]<=4 $[3]<=5 $[4]<=5 $[5]<=5 $[6]<=5 $[7]<=5
                       $[8]<=4 $[9]<=4 $[10]<=4 $[11]<=4 $.
              Pcase: f1[9] <= 6.
                Reducible.
              Pcase: h[1] > 6.
                Hubcap $[1]<=4 $[2]<=4 $[3]<=5 $[4]<=5 $[5]<=5 $[6]<=5 $[7]<=5
                       $[8]<=4 $[9]<=5 $[10]<=4 $[11]<=4 $.
              Pcase: f1[1] <= 6.
                Reducible.
              Pcase L7_1: h[2] > 5.
                Pcase: h[3] > 5.
                  Hubcap $[1]<=5 $[2]<=3 $[3]<=5 $[4]<=5 $[5]<=5 $[6]<=5 $[7]<=5
                         $[8]<=4 $[9]<=5 $[10]<=4 $[11]<=4 $.
                Pcase: h[4] <= 6.
                  Reducible.
                Pcase: h[11] <= 5.
                  Reducible.
                Pcase: h[5] > 5.
                  Hubcap $[1]<=5 $[2]<=4 $[3]<=5 $[4]<=4 $[5]<=5 $[6]<=5 $[7]<=5
                         $[8]<=4 $[9]<=5 $[10]<=4 $[11]<=4 $.
                Hubcap $[1]<=5 $[2]<=4 $[3]<=5 $[4]<=5 $[5]<=5 $[7]<=5 $[8]<=4
                       $[10]<=4 $[11]<=4 $[6,9]<=9 $.
              Pcase: h[9] > 5.
                Similar to *L7_1[2].
              Pcase: h[3] <= 6.
                Reducible.
              Pcase: h[8] <= 6.
                Reducible.
              Pcase: h[4] > 5.
                Hubcap $[1]<=5 $[2]<=4 $[3]<=4 $[4]<=5 $[5]<=5 $[6]<=5 $[7]<=5
                       $[8]<=4 $[9]<=5 $[10]<=4 $[11]<=4 $.
              Hubcap $[1]<=5 $[2]<=4 $[3]<=5 $[4]<=5 $[6]<=5 $[8]<=4 $[9]<=5
                     $[10]<=4 $[11]<=4 $[5,7]<=9 $.
            Pcase: s[9] > 5.
              Similar to L1_1[7].
            Pcase: s[10] > 5.
              Hubcap $[1]<=5 $[2]<=4 $[3]<=5 $[4]<=5 $[5]<=5 $[6]<=5 $[7]<=4
                     $[8]<=5 $[10]<=5 $[9,11]<=7 $.
            Pcase: h[2] > 6.
              Hubcap $[1]<=4 $[2]<=4 $[3]<=5 $[4]<=5 $[5]<=5 $[6]<=5 $[7]<=4
                     $[8]<=5 $[9]<=4 $[10]<=5 $[11]<=4 $.
            Pcase: f1[1] <= 5.
              Reducible.
            Pcase: h[8] > 6.
              Hubcap $[1]<=5 $[2]<=4 $[3]<=5 $[4]<=5 $[5]<=5 $[6]<=5 $[7]<=4
                     $[8]<=4 $[9]<=4 $[10]<=5 $[11]<=4 $.
            Pcase: f1[8] <= 5.
              Reducible.
            Pcase: h[9] > 6.
              Hubcap $[1]<=5 $[2]<=4 $[3]<=5 $[4]<=5 $[5]<=5 $[6]<=5 $[7]<=4
                     $[8]<=4 $[9]<=4 $[10]<=5 $[11]<=4 $.
            Pcase: f1[8] <= 6.
              Reducible.
            Pcase: h[1] > 6.
              Hubcap $[1]<=4 $[2]<=4 $[3]<=5 $[4]<=5 $[5]<=5 $[6]<=5 $[7]<=4
                     $[8]<=5 $[9]<=4 $[10]<=5 $[11]<=4 $.
            Pcase: f1[1] <= 6.
              Reducible.
            Pcase L6_1: h[2] > 5.
              Pcase: h[3] > 5.
                Hubcap $[1]<=5 $[2]<=3 $[3]<=5 $[4]<=5 $[5]<=5 $[6]<=5 $[7]<=4
                       $[8]<=5 $[9]<=4 $[10]<=5 $[11]<=4 $.
              Pcase: h[4] <= 6.
                Reducible.
              Pcase: h[11] <= 5.
                Reducible.
              Pcase: h[5] > 5.
                Hubcap $[1]<=5 $[2]<=4 $[3]<=5 $[4]<=4 $[5]<=5 $[6]<=5 $[7]<=4
                       $[8]<=5 $[9]<=4 $[10]<=5 $[11]<=4 $.
              Hubcap $[1]<=5 $[2]<=4 $[3]<=5 $[4]<=5 $[5]<=5 $[7]<=4 $[8]<=5
                     $[9]<=4 $[11]<=4 $[6,10]<=9 $.
            Pcase: h[8] > 5.
              Similar to *L6_1[3].
            Pcase: h[3] <= 6.
              Reducible.
            Pcase: h[7] <= 6.
              Reducible.
            Hubcap $[2]<=4 $[3]<=5 $[4]<=5 $[5]<=5 $[6]<=5 $[7]<=4 $[9]<=4
                   $[10]<=5 $[11]<=4 $[1,8]<=9 $.
          Pcase: s[8] > 5.
            Similar to L1_1[6].
          Pcase: s[9] > 5.
            Hubcap $[1]<=5 $[2]<=4 $[3]<=5 $[4]<=5 $[5]<=5 $[6]<=4 $[7]<=5
                   $[8]<=4 $[9]<=5 $[10]<=4 $[11]<=4 $.
          Pcase: s[10] > 5.
            Hubcap $[1]<=5 $[2]<=4 $[3]<=5 $[4]<=5 $[5]<=5 $[6]<=4 $[7]<=5
                   $[8]<=4 $[9]<=4 $[10]<=5 $[11]<=4 $.
          Pcase: h[2] > 6.
            Hubcap $[1]<=4 $[2]<=4 $[3]<=5 $[4]<=5 $[5]<=5 $[6]<=4 $[7]<=5
                   $[8]<=4 $[9]<=5 $[10]<=5 $[11]<=4 $.
          Pcase: f1[1] <= 5.
            Reducible.
          Pcase: h[7] > 6.
            Hubcap $[1]<=5 $[2]<=4 $[3]<=5 $[4]<=5 $[5]<=5 $[6]<=4 $[7]<=4
                   $[8]<=4 $[9]<=5 $[10]<=5 $[11]<=4 $.
          Pcase: f1[7] <= 5.
            Reducible.
          Pcase: h[8] > 6.
            Hubcap $[1]<=5 $[2]<=4 $[3]<=5 $[4]<=5 $[5]<=5 $[6]<=4 $[7]<=4
                   $[8]<=4 $[9]<=5 $[10]<=5 $[11]<=4 $.
          Pcase: f1[7] <= 6.
            Reducible.
          Pcase: h[1] > 6.
            Hubcap $[1]<=4 $[2]<=4 $[3]<=5 $[4]<=5 $[5]<=5 $[6]<=4 $[7]<=5
                   $[8]<=4 $[9]<=5 $[10]<=5 $[11]<=4 $.
          Pcase: f1[1] <= 6.
            Reducible.
          Pcase L5_1: h[2] > 5.
            Pcase: h[3] > 5.
              Hubcap $[1]<=5 $[2]<=3 $[3]<=5 $[4]<=5 $[5]<=5 $[6]<=4 $[7]<=5
                     $[8]<=4 $[9]<=5 $[10]<=5 $[11]<=4 $.
            Pcase: h[4] <= 6.
              Reducible.
            Pcase: h[11] <= 5.
              Reducible.
            Pcase: h[5] > 5.
              Hubcap $[1]<=5 $[2]<=4 $[3]<=5 $[4]<=4 $[5]<=5 $[6]<=4 $[7]<=5
                     $[8]<=4 $[9]<=5 $[10]<=5 $[11]<=4 $.
            Hubcap $[1]<=5 $[2]<=4 $[3]<=5 $[4]<=5 $[5]<=5 $[6]<=4 $[8]<=4
                   $[9]<=5 $[11]<=4 $[7,10]<=9 $.
          Pcase: h[7] > 5.
            Similar to *L5_1[4].
          Pcase: h[3] <= 6.
            Reducible.
          Pcase: h[6] <= 6.
            Reducible.
          Hubcap $[1]<=5 $[2]<=4 $[4]<=5 $[6]<=4 $[7]<=5 $[8]<=4 $[9]<=5
                 $[10]<=5 $[11]<=4 $[3,5]<=9 $.
        Pcase: s[7] > 5.
          Similar to L1_1[5].
        Pcase: s[8] > 5.
          Hubcap $[1]<=5 $[2]<=4 $[3]<=5 $[4]<=5 $[5]<=4 $[6]<=5 $[7]<=4
                 $[8]<=5 $[11]<=4 $[9,10]<=9 $.
        Pcase: s[9] > 5.
          Hubcap $[1]<=5 $[2]<=4 $[3]<=5 $[4]<=5 $[5]<=4 $[6]<=5 $[7]<=4 $[8]<=4
                 $[9]<=5 $[10]<=4 $[11]<=4 $.
        Pcase: s[10] <= 5.
          Similar to L4_1[5].
        Hubcap $[1]<=5 $[2]<=4 $[3]<=5 $[4]<=5 $[5]<=4 $[6]<=5 $[7]<=4 $[8]<=5
               $[9]<=4 $[10]<=5 $[11]<=4 $.
      Pcase: s[6] > 5.
        Similar to L1_1[4].
      Pcase L3_2: s[7] <= 5.
        Pcase L4_1: s[8] <= 5.
          Pcase: s[9] <= 5.
            Similar to L3_1[4].
          Pcase: s[10] > 5.
            Similar to L1_1[8].
          Hubcap $[1]<=5 $[2]<=4 $[3]<=5 $[4]<=4 $[5]<=5 $[6]<=4 $[7]<=5 $[8]<=4
                 $[9]<=5 $[10]<=4 $[11]<=4 $.
        Pcase: s[9] > 5.
          Similar to L1_1[7].
        Pcase: s[10] <= 5.
          Similar to L4_1[7].
        Hubcap $[1]<=5 $[2]<=4 $[3]<=5 $[4]<=4 $[5]<=5 $[6]<=4 $[7]<=4 $[8]<=5
               $[9]<=4 $[10]<=5 $[11]<=4 $.
      Pcase: s[8] > 5.
        Similar to L1_1[6].
      Pcase: s[10] <= 5.
        Similar to *L3_2[6].
      Pcase: s[9] > 5.
        Similar to L1_1[8].
      Hubcap $[1]<=5 $[2]<=4 $[3]<=5 $[4]<=4 $[5]<=5 $[6]<=4 $[7]<=5 $[8]<=4
             $[9]<=4 $[10]<=5 $[11]<=4 $.
    Pcase: s[5] > 5.
      Similar to L1_1[3].
    Pcase L2_2: s[6] <= 5.
      Pcase: s[7] <= 5.
        Similar to L2_1[3].
      Pcase: s[8] > 5.
        Similar to L1_1[6].
      Hubcap $[1]<=5 $[2]<=4 $[3]<=4 $[4]<=5 $[5]<=4 $[6]<=4 $[7]<=5 $[8]<=4
             $[9]<=5 $[10]<=5 $[11]<=4 $.
    Pcase: s[7] > 5.
      Similar to L1_1[5].
    Pcase: s[8] <= 5.
      Similar to L2_2[5].
    Pcase: s[9] > 5.
      Similar to L1_1[7].
    Pcase: s[10] <= 5.
      Similar to L2_1[7].
    Hubcap $[1]<=5 $[2]<=4 $[3]<=4 $[4]<=5 $[5]<=4 $[6]<=5 $[7]<=4 $[8]<=5
           $[9]<=4 $[10]<=5 $[11]<=4 $.
  Pcase: s[4] > 5.
    Similar to L1_1[2].
  Pcase: s[5] <= 5.
    Similar to L1_2[2].
  Pcase: s[6] > 5.
    Similar to L1_1[4].
  Pcase: s[7] <= 5.
    Similar to L1_2[4].
  Pcase: s[8] > 5.
    Similar to L1_1[6].
  Pcase: s[9] > 5.
    Similar to L1_2[8].
  Pcase: s[10] > 5.
    Similar to L1_2[6].
  Pcase: h[2] > 5.
    Similar to L1_2[6].
  Pcase: h[3] > 5.
    Similar to L1_2[6].
  Pcase: h[4] > 5.
    Similar to L1_2[6].
  Pcase: h[5] > 5.
    Similar to L1_2[6].
  Pcase: h[6] > 5.
    Similar to L1_2[6].
  Pcase: h[7] > 5.
    Similar to L1_2[6].
  Pcase: h[8] > 5.
    Similar to L1_2[6].
  Pcase: h[9] > 5.
    Similar to L1_2[6].
  Pcase: h[10] > 5.
    Similar to L1_2[6].
  Pcase: h[11] > 5.
    Similar to L1_2[6].
  Pcase: h[1] > 5.
    Similar to L1_2[6].
  Pcase: f1[1] > 5.
    Similar to L1_2[6].
  Pcase: f1[3] > 5.
    Similar to L1_2[6].
  Pcase: f1[5] > 5.
    Similar to L1_2[6].
  Pcase: f1[7] > 5.
    Similar to L1_2[6].
  Reducible.
Pcase: s[2] > 5.
  Similar to L0_3[1].
Pcase: s[3] > 5.
  Similar to L0_3[2].
Pcase: s[4] > 5.
  Similar to L0_3[3].
Pcase: s[5] > 5.
  Similar to L0_3[4].
Pcase: s[6] > 5.
  Similar to L0_3[5].
Pcase: s[7] > 5.
  Similar to L0_3[6].
Pcase: s[8] > 5.
  Similar to L0_3[7].
Pcase: s[9] > 5.
  Similar to L0_3[8].
Pcase: s[10] > 5.
  Similar to L0_3[9].
Pcase: s[11] > 5.
  Similar to L0_3[10].
Reducible.
Qed.
