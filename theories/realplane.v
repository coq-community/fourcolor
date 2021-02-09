(* (c) Copyright 2006-2018 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From fourcolor
Require Import real.

(******************************************************************************)
(*  An elementary formalization of the real plane topology required to state  *)
(* the Four Color Theorem. All definitions here are parametrized by a Real    *)
(* structure R:                                                               *)
(*     point R == type of points in the R x R plane. Since Real.val R is      *)
(*                a type of denotations of real numbers, point R would be     *)
(*                more accurately described as a type of point denotations.   *)
(*                We do not define the value equality on points, however, as  *)
(*                it is not needed for stating nor proving the Four Color     *)
(*                Theorem.                                                    *)
(*    region R == type for point sets, i.e., regions in the common rather     *)
(*                than topological sense. We don't enforce extensionality: a  *)
(*                region r could contain some but not all denotations of a    *)
(*                point. However we generally assume extensionality in the    *)
(*                other definitions below, as we only use topologically open  *)
(*                or closed regions, which are extensional, in this proof.    *)
(*       map R == type for point relations. This allows for arbitrary         *)
(*                connectivity in a map (see plain and simple maps below).    *)
(*  interval R == type of open intervals on R (isomorphic to point R).        *)
(*  rectangle R == type of open rectangles in R x R.                          *)
(*  union r1 r2 == the union (region) of r1 and r2 : region R.                *)
(*  intersect r1 r2 == the intersection (region) of r1 and r2 : region R.     *)
(*                 (assuming r1 and r2 are extensional).                      *)
(*  subregion r1 r2 <-> region r1 is included in region r2.                   *)
(*   nonempty r <-> reqion r1 is not empty.                                   *)
(*   meet r1 r2 <-> regions r1 and r2 meet (intensionally).                   *)
(*  plain_map m <-> m is a 'plain' map, i.e., a partial equivalence relation, *)
(*               or PER, whose classes are the regions of m.                  *)
(*      cover m == the region covered by a plain map m; the region of a point *)
(*               z in cover m is (m z), as cover m z := m z z.                *)
(*  submap m1 m2 <-> map m1 is included in m2: each region of m1 is included  *)
(*               in a (possibly larger) region of m2.                         *)
(*  at_most_regions n m <-> plain map m has at most n : nat regions.          *)
(*      open r <-> r is a topologically open (hence extensional) regions.     *)
(*  connected r <-> r is a topologically connected (extensional) region.      *)
(*  simple_map m <-> m is a simple map: plain with open and connected regions *)
(*               (i.e., regions of m are regions in the topological sense).   *)
(*  finite_simple_map m <-> m is a simple map with finitely many regions.     *)
(*   closure r == topological closure of region r.                            *)
(*  border m z1 z2 == the common border between the regions of z1 and z2 in   *)
(*               map m, assuming z1 and z2 are in different regions of m.     *)
(*  not_corner m == the set of non-corner points in map m, that belong to the *)
(*               closure of at most two regions of m.                         *)
(*  adjacent m z1 z2 <-> the regions of z1 and z2 in m are adjacent: they     *)
(*               have a non-corner common border point.                       *)
(*  coloring m k <-> the map m admits k as a coloring; k is also represented  *)
(*               as a map, whose regions are the sets of points with the same *)
(*               color. Thus k must be a plain map covering the some points   *)
(*               as m, assigns the same color to each region of m (i.e., the  *)
(*               regions are a refinement of the color partition k), and      *)
(*               assign different colors to points of adjacent regions.       *)
(*  colorable_with n m <-> map m admits a coloring with at most n regions.    *)
(* As this file comprises the second part of the background definitions for   *)
(* the Four Color Theorem, it avoids using any of the syntactic extension     *)
(* facilities of Coq, much like the first part (real.v). Coercions, from      *)
(* intervals and rectangles to sets, and between map properties, are hidden   *)
(* a RealPlanCoercions submodule.                                             *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Definitions.

Variable R : Real.structure.

(* Elementary geometry. *)

Inductive point : Type := Point (x y : Real.val R).

Definition region : Type := point -> Prop.

Definition map : Type := point -> region.

Inductive interval : Type := Interval (x y : Real.val R).

Inductive rectangle : Type := Rectangle (hspan vspan : interval).

Definition in_interval (s : interval) : Real.set R :=
  fun t => let ' Interval x y := s in Real.lt x t /\ Real.lt t y.

Definition in_rectangle rr : region :=
  fun z => let ' Rectangle hspan vspan := rr in let ' Point x y := z in
  in_interval hspan x /\ in_interval vspan y.

(* Elementary set theory for the plane. *)

Definition union (r1 r2 : region) : region := fun z => r1 z \/ r2 z.

Definition intersect (r1 r2 : region) : region := fun z => r1 z /\ r2 z.

Definition nonempty (r : region) : Prop := exists z : point, r z.

Definition subregion (r1 r2 : region) : Prop := forall z : point, r1 z -> r2 z.

Definition meet (r1 r2 : region) : Prop := nonempty (intersect r1 r2).

(* Maps are represented as relations; proper map are partial equivalence  *)
(* relations (PERs).                                                      *)

Record plain_map (m : map) : Prop := PlainMap {
  map_sym z1 z2 : m z1 z2 -> m z2 z1;
  map_trans z1 z2 : m z1 z2 -> subregion (m z2) (m z1)
}.

Definition cover (m : map) : region := fun z => m z z.

Definition submap (m1 m2 : map) : Prop := forall z, subregion (m1 z) (m2 z).

Definition at_most_regions (n : nat) (m : map) :=
  exists f, forall z, cover m z -> exists2 i : nat, Peano.lt i n & m (f i) z.

(* Elementary topology. *)

Definition open (r : region) : Prop :=
  forall z, r z -> exists2 u, in_rectangle u z & subregion (in_rectangle u) r.

Definition closure (r : region) : region :=
  fun z => forall u, open u -> u z -> meet r u.

Definition connected (r : region) : Prop :=
  forall u v, open u -> open v -> subregion r (union u v) ->
  meet u r -> meet v r -> meet u v.

Record simple_map (m : map) : Prop := SimpleMap {
  simple_map_plain : plain_map m;
  simple_map_open z : open (m z);
  simple_map_connected z : connected (m z)
}.

Record finite_simple_map (m : map) : Prop := FiniteSimpleMap {
  finite_simple_map_simple : simple_map m;
  finite_simple_map_finite : exists n, at_most_regions n m
}.

(* Borders, corners, adjacency and coloring. *)

Definition border (m : map) (z1 z2 : point) : region :=
  intersect (closure (m z1)) (closure (m z2)).

Definition corner_map (m : map) (z : point) : map :=
  fun z1 z2 => m z1 z2 /\ closure (m z1) z.

Definition not_corner (m : map) : region :=
  fun z => at_most_regions 2 (corner_map m z).

Definition adjacent (m : map) (z1 z2 : point) : Prop :=
  ~ m z1 z2 /\ meet (not_corner m) (border m z1 z2).

Record coloring (m k : map) : Prop := Coloring {
  coloring_plain : plain_map k;
  coloring_cover : subregion (cover k) (cover m);
  coloring_consistent : submap m k;
  coloring_adjacent z1 z2 : adjacent m z1 z2 -> ~ k z1 z2
}.

Definition colorable_with (n : nat) (m : map) : Prop :=
  exists2 k, coloring m k & at_most_regions n k.

End Definitions.

Module RealPlaneCoercions.

Identity Coercion in_region : region >-> Funclass.
Identity Coercion in_map : map >-> Funclass.
Coercion in_interval : interval >-> Real.set.
Coercion in_rectangle : rectangle >-> region.
Coercion simple_map_plain : simple_map >-> plain_map.
Coercion finite_simple_map_simple : finite_simple_map >-> simple_map.
Coercion coloring_plain : coloring >-> plain_map.

End RealPlaneCoercions.
