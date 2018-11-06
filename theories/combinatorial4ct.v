(* (c) Copyright 2006-2018 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrfun ssrbool eqtype ssrnat seq choice fintype path fingraph.
From fourcolor
Require Import hypermap geometry color coloring cube present.
From fourcolor
Require Import unavoidability reducibility.

(******************************************************************************)
(*   The (constructive) proof of the Four Color Theorem for finite            *)
(* combinatorial hypermaps.                                                   *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Theorem four_color_hypermap G : planar_bridgeless G -> four_colorable G.
Proof.
move=> geoG; apply: cube_colorable.
have{geoG} geoGQ: planar_bridgeless_plain_precubic (cube G).
  split; last exact/cubic_precubic/cubic_cube.
  split; last exact: plain_cube.
  by split; [rewrite planar_cube | rewrite bridgeless_cube]; apply: geoG.
pose n := #|cube G|.+1; move: geoGQ (leqnn n); rewrite {1}/n.
elim: {G}n (cube G) => // n IHn G geoG; rewrite ltnS leq_eqVlt.
case/predU1P=> [Dn | /IHn]; [rewrite -{n}Dn in IHn | exact].
have [// | noncolG] := decide_colorable G.
by have [] := @unavoidability the_reducibility G.
Qed.
