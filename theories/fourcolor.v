(* (c) Copyright 2006-2018 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From fourcolor
Require Import real realplane.
From fourcolor
Require combinatorial4ct discretize finitize.

(******************************************************************************)
(*   This files contains the proof of the high-level statement of the Four    *)
(* Color Theorem, whose statement uses only the elementary real topology      *)
(* defined in libraies real and realplane. The theorem is stated for an       *)
(* arbitrary model of the real line, which we show in separate libraries      *)
(* (dedekind and realcategorical) is equivalent to assumint the classical     *)
(* excluded middle axiom.                                                     *)
(*   We only import the real and realplane libraries, which do not introduce  *)
(* any extra-logical context, in particular no new notation, so that the      *)
(* interpretation of the text below is as transparent as possible.            *)
(*   Accordingly we use qualified names refer to the supporting result in the *)
(* finitize, discretize and combinatorial4ct libraries, and do not rely on    *)
(* the ssreflect extensions in the formulation of the final arguments.        *)
(******************************************************************************)

Section FourColorTheorem.

Variable Rmodel : Real.model.
Let R := Real.model_structure Rmodel.
Implicit Type m : map R.

Theorem four_color_finite m : finite_simple_map m -> colorable_with 4 m.
Proof.
intros fin_m.
pose proof (discretize.discretize_to_hypermap fin_m) as [G planarG colG].
exact (colG (combinatorial4ct.four_color_hypermap planarG)).
Qed.

Theorem four_color m : simple_map m -> colorable_with 4 m.
Proof. revert m; exact (finitize.compactness_extension four_color_finite). Qed.

End FourColorTheorem.