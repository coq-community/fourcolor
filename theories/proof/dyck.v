(* (c) Copyright 2006-2018 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.

(******************************************************************************)
(* We define two combinatorial functions:                                     *)
(*        dyck n == the number of balanced bracket words of length n          *)
(*  gen_dyck m n == the number of balanced bracket word fragments of length n *)
(*                  with m-1 extra closing brackets: dyck n = gen_dyck 1 n    *)
(* These ``Dyck numbers'', are closely related to the well-known Catalan      *)
(* numbers,                                                                   *)
(*            1   /2n\                                                        *)
(*     C_n = --- (    )                                                       *)
(*           n+1  \ n/                                                        *)
(* More precisely, dick n = C_(n/2) if n is even, and 0 if n is odd; the      *)
(* gen_dyck m n are similarly related to the Catalan-Fuss (or Raney) numbers  *)
(* A_{(n+1-m)/2}(2,m); however they are defined using a non-standard          *)
(* recurrence that simplifies the correctness proof of the initial data of    *)
(* the reducibility check. Indeed, Dyck numbers are the only link between the *)
(* initial color and (chromo)gram trees.                                      *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Fixpoint gen_dyck m n {struct n} :=
  match n, m with
  | 0, 1 => 1
  | n'.+1, m'.+1 => gen_dyck m.+1 n' + gen_dyck m' n'
  | _, _ => 0
  end.

Definition dyck := gen_dyck 1.

Lemma gen_dyck_max m n : n.+1 < m -> gen_dyck m n = 0.
Proof.
elim: n m => [|n IHn] [] //= => [[] // | m lt_n1_m].
by rewrite !IHn // 2?ltnW.
Qed.

Lemma gen_dyck_all_close m : gen_dyck m.+1 m = 1.
Proof. by elim: m => //= m ->; rewrite gen_dyck_max. Qed.

Lemma even_dyck_pos n : 0 < dyck n.*2.
Proof.
rewrite -[n.*2]addn0 /dyck; elim: n {-1}0 => [|n IHn] m.
  by rewrite gen_dyck_all_close.
by rewrite doubleS addSnnS addSn ltn_addr.
Qed.
