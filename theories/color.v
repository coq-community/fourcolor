(* (c) Copyright 2006-2018 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import fintype.

(******************************************************************************)
(* The four colors, with color sum (xor) and comparison:                      *)
(*       color == the finite type of colors, with values Color0 - Color3.     *)
(* palette c0 c1 c2 c3 c == cI when c = colorI; Notation for match c with ... *)
(*     cbit0 c == the lower bit of color c (= true for Color1 and Color3).    *)
(*     cbit1 c == the higher bit of color c (= true for Color2 and Color3).   *)
(* ccons b1 b0 == the Color 2b1 + b0.                                         *)
(*    c1 +c c2 == the bitwise sum of colors c1 and c2.                        *)
(*   edge_perm == a finite type enumerating permutations of nonzero colors.   *)
(*                EpermIJK denotes the permutation mapping Color1 to ColorI,  *)
(*                Color2 to ColorJ, Color3 to ColorK, e.g., Eperm132 swaps    *)
(*                Color2 and Color3, while Eperm123 is the identity.          *)
(*     permc g == coercion of g : edge_perm to a color -> color function.     *)
(* inv_eperm g == the edge_perm inverse of g.                                 *)
(*  edge_rot c == the even edge_perm mapping c to Color1, if c != Color0.     *)
(*      colseq := seq color (a perimeter / edge perimeter coloring).          *)
(* count_cbit1 s == the number of times cbit1 is set in s : colseq.           *)
(* head_color s == the first color in s : colseq, defaulting to Color0.       *)
(*      trace s == the trace (edge coloring) corresponding to a perimeter     *)
(*                 coloring s : colseq; the i'th color in trace s is the      *)
(*                 bitwise sum of colors i and i+1[mod size s] in s.          *)
(*    urtrace s == the right-rotated trace of s (= rotr 1 (trace s)).         *)
(*     ptrace s == the partial trace of s: trace s less its last color, which *)
(*                 is redundant as it is the sum of the other ones.           *)
(*       sumt t == the bitwise sum of all colors in t.                        *)
(*     ctrace t == completes a partial trace t by computing the last color.   *)
(* untrace c0 t == the coloring with head_color c0 and trace t.               *)
(* proper_trace t <=> t does not start with Color0: a trace obtained from a   *)
(*                 proper coloring (one which does not contain identical      *)
(*                 adjacent colors) cannot contain Color0 at all; so we use   *)
(*                 [:: Color0] to signal failure of some trace operations.    *)
(*    permt g t == map g : edge_perm over t : colseq.                         *)
(*      ttail t == the seminormalised tail of a trace t, obtained by mapping  *)
(*                 edge_rot c over behead t, when c = head_color t is not     *)
(*                 Color0, otherwise ttail fails, returning [:: Color0].      *)
(*  even_tail t <=> Color2 appears before Color3 in t.                        *)
(*  even_trace t <=> if t is proper, there is an even permutation of edge     *)
(*                 colors of t where colors appear in the 1, 2, 3 order.      *)
(*  even_perm t == a permutation of Color2-3 that maps t to an even trace.    *)
(*     etrace t == a Color2-3 permutation of t that is even.                  *)
(*      etail t == the normalised, even tail of t: colors appear in order in  *)
(*                 Color1 :: etail t which is an edge color permutation of t. *)
(*    eptrace s == the standardized tail of the partial trace of s.           *)
(*              := etail (ptrace s).                                          *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive color : predArgType := Color0 | Color1 | Color2 | Color3.

Notation palette c0 c1 c2 c3 := (fun c =>
  match c with Color0 => c0 | Color1 => c1 | Color2 => c2 | Color3 => c3 end).

(* Color comparison and sum; sum is used to compute traces, so it is taken as *)
(* primitive.                                                                 *)

Definition addc : color -> color -> color :=
  palette id (palette Color1 Color0 Color3 Color2)
             (palette Color2 Color3 Color0 Color1)
             (palette Color3 Color2 Color1 Color0).

Notation "c1 '+c' c2" := (addc c1 c2) (at level 50).

Definition eqc (c c' : color) : bool :=
  if c +c c' is Color0 then true else false.

(* Properties of equality, and canonical dataSet.                             *)

Lemma eqcP : Equality.axiom eqc.
Proof. by do 2!case; constructor. Qed.

Canonical color_eqMixin := EqMixin eqcP.
Canonical color_eqType := EqType color color_eqMixin.

Arguments eqcP {c1 c2} : rename.

Lemma eqcE : eqc = eq_op.
Proof. by []. Qed.

(* Algebraic properties of addc. *)

Lemma addcA : associative addc. Proof. by do 3!case. Qed.
Lemma addcC : commutative addc. Proof. by do 2!case. Qed.
Lemma add0c : left_id Color0 addc. Proof. by case. Qed.
Lemma addc0 : right_id Color0 addc. Proof. by case. Qed.
Lemma addcc : self_inverse Color0 addc. Proof. by case. Qed.
Lemma addKc : left_loop id addc. Proof. by do 2!case. Qed.
Lemma addcK : right_loop id addc. Proof. by do 2!case. Qed.
Lemma addcI c : injective (addc c). Proof. exact: can_inj (addKc c). Qed.

Lemma addc_eq0 c1 c2 : (c1 +c c2 == Color0) = (c1 == c2).
Proof. by case: c1; case: c2. Qed.

Arguments addcI c [c1 c2] : rename.

(* Colors as bit vectors *)

Definition cbit0 := palette false true false true.

Definition cbit1 := palette false false true true.

Definition ccons b1 b0 := match b1, b0 with
  | false, false => Color0
  | false, true => Color1
  | true, false => Color2
  | true, true => Color3
  end.

(* Bit properties. *)

Lemma ccons_cbits c : ccons (cbit1 c) (cbit0 c) = c.
Proof. by case: c. Qed.

Lemma cbit1_ccons b1 b0 : cbit1 (ccons b1 b0) = b1.
Proof. by case: b1; case: b0. Qed.

Lemma cbit0_ccons b1 b0 : cbit0 (ccons b1 b0) = b0.
Proof. by case: b1; case: b0. Qed.

Lemma cbit1_addc c1 c2 : cbit1 (c1 +c c2) = cbit1 c1 (+) cbit1 c2.
Proof. by case: c1; case: c2. Qed.

Lemma cbit0_addc c1 c2 : cbit0 (c1 +c c2) = cbit0 c1 (+) cbit0 c2.
Proof. by case: c1; case: c2. Qed.

(* The six "edge" permutations that leave Color0 unchanged. *)

Inductive edge_perm : Set :=
  | Eperm123 : edge_perm
  | Eperm132 : edge_perm
  | Eperm213 : edge_perm
  | Eperm231 : edge_perm
  | Eperm312 : edge_perm
  | Eperm321 : edge_perm.

Definition permc g :=
  match g with
  | Eperm123 => fun c => c
  | Eperm132 => palette Color0 Color1 Color3 Color2
  | Eperm213 => palette Color0 Color2 Color1 Color3
  | Eperm231 => palette Color0 Color2 Color3 Color1
  | Eperm312 => palette Color0 Color3 Color1 Color2
  | Eperm321 => palette Color0 Color3 Color2 Color1
  end.

Coercion permc : edge_perm >-> Funclass.

Definition inv_eperm g :=
  match g with
  | Eperm312 => Eperm231
  | Eperm231 => Eperm312
  | _ => g
  end.

Lemma inv_epermK : involutive inv_eperm.
Proof. by case. Qed.

Lemma inv_permc (g : edge_perm) : cancel g (inv_eperm g).
Proof. by case: g => [] []. Qed.

Lemma permc_inv g : cancel (inv_eperm g) g.
Proof. by case: g => [] []. Qed.

Lemma permc_inj (g : edge_perm) : injective g.
Proof. exact (can_inj (inv_permc g)). Qed.

Lemma permc_addc (g : edge_perm) c1 c2 : g (c1 +c c2) = g c1 +c g c2.
Proof. by case: g; case: c1; case: c2. Qed.

Lemma permc0 (g : edge_perm) : g Color0 = Color0.
Proof. by case: g. Qed.

Lemma color_inj_permc f :
  injective f -> f Color0 = Color0 -> {g : edge_perm | f =1 g}.
Proof.
move/inj_eq=> injf f0; have Ef0 := injf Color0; rewrite f0 in Ef0.
case f1: (f Color1) (Ef0 Color1) (injf Color1) => // _ Ef1;
case f2: (f Color2) (Ef0 Color2) (Ef1 Color2) {injf}(injf Color2) => // _ _ Ef2;
   [ exists Eperm123 | exists Eperm132 | exists Eperm213
   | exists Eperm231 | exists Eperm312 | exists Eperm321] => [] [] //;
 by case: (f Color3) (Ef0 Color3) (Ef1 Color3) (Ef2 Color3).
Qed.

Lemma other_colors c : 
  c != Color0 -> pred4 Color0 c (Eperm312 c) (Eperm231 c) =i color.
Proof. by case: c => // _ []. Qed.

(******************************************************************************)
(*   Basic operations on edge traces = pairwise sums of the list of colors on *)
(* a configuration perimeter. Many of these operations use permutations of    *)
(* the non-zero colors, so we introduce an explicit enumeration of these six  *)
(* permutations. A ``proper'' trace, one that begins with a non-zero color,   *)
(* has a ``normal'' tail, obtained by applying the rotation that sends the    *)
(* first color to Color1 to the rest of the trace. A trace is even if Color3  *)
(* does not occur before Color2 in its tail. To cut our work in half, we only *)
(* consider even traces in our algorithm, as the match relation is invariant  *)
(* under swapping Color2 and Color3. The coloring function outputs directly   *)
(* the even trace tail of colorings, so we prove here that this is invariant  *)
(* under permutations of the coloring.                                        *)
(*   Allowing Color0 in traces allows us to carry fewer side conditions in    *)
(* our lemmas, and gives us a convenient ``bad'' value as well.               *)
(*   Finally, we define a completion operation that adds the last ``cyclic''  *)
(* sum to a trace, and prove its basic properties. These will be used with    *)
(* the ``canonical'' match relation.                                          *)
(******************************************************************************)

(* Boolean correctness predicate *)

Definition colseq : predArgType := seq color.
Canonical colseq_eqType := [eqType of colseq].

Definition head_color : colseq -> color := head Color0.

Definition proper_trace et := head_color et != Color0.

(******************************************************************************)
(* Conversion from color lists to traces is done in two steps: compute the    *)
(* pairwise sum to get a partial (linear) trace, then append the last color,  *)
(* which can be computed as the sum of the partial trace, to get a full       *)
(* (cyclic) trace. The trace computation inverse just computes partial sums.  *)
(******************************************************************************)

Definition ptrace (lc : colseq) : colseq :=
  if lc is c :: lc' then pairmap addc c lc' else [::].

Definition permt (g : edge_perm) : colseq -> colseq := map g.

Definition sumt : colseq -> color := foldr addc Color0.

Definition ctrace (et : colseq) : colseq := rcons et (sumt et).

Definition trace (lc : colseq) : colseq :=
  if lc is _ :: _ then ctrace (ptrace lc) else [::].

Definition urtrace (lc : colseq) : colseq := pairmap addc (last Color0 lc) lc.

Definition untrace c0 (et : colseq) : colseq :=
  scanl addc c0 (belast Color0 et).

(* Trace normalization. *)

Definition edge_rot := palette Eperm123 Eperm123 Eperm312 Eperm231.

Definition ttail (et : colseq) : colseq :=
  if proper_trace et then
    if et is c :: et' then permt (edge_rot c) et' else [::]
  else [:: Color0].

Definition even_tail : colseq -> bool :=
  foldr (fun c b => palette b b true false c) true.

Definition even_trace et := even_tail (ttail et).

Definition etrace_perm et := if even_trace et then Eperm123 else Eperm132.

Definition etrace et := permt (etrace_perm et) et.

Definition etail et := permt (etrace_perm et) (ttail et).

Definition eptrace lc := etail (ptrace lc).

(* Counting cbit1, used to validate the initial tree construction.  *)

Definition count_cbit1 : colseq -> nat := foldr (fun c n => cbit1 c + n) 0.

(* Lemmas for edge permutations : the standard iso lemmas, and commutation    *)
(* with addc (proved by brute force).                                         *)

(* Trace permutation. *)

Lemma permt_id et : permt Eperm123 et = et.
Proof. exact: map_id. Qed.

Lemma etrace_id et : permt Eperm132 (permt Eperm132 et) = et.
Proof. exact: (mapK (inv_permc Eperm132)). Qed.

Lemma permc_eq0 (g : edge_perm) c : (g c == Color0) = (c == Color0).
Proof. by case: g; case: c. Qed.

Lemma memc0_permt g et : (Color0 \in permt g et) = (Color0 \in et).
Proof.
by elim: et => [|e et IHet] //=; rewrite !inE IHet !(eq_sym Color0) permc_eq0.
Qed.

Lemma proper_permt g et : proper_trace (permt g et) = proper_trace et.
Proof. by case: g; case: et => // [[]]. Qed.

Lemma memc0_ttail et :
  (Color0 \in ttail et) = ~~ proper_trace et || (Color0 \in et).
Proof. by case: et => [|[] et]; rewrite /ttail //= memc0_permt. Qed.

(* Even and tail permutations. *)

Lemma even_etail et : even_tail (etail et).
Proof.
rewrite /etail /etrace_perm; case: ifP; first by rewrite permt_id.
by rewrite /even_trace; elim: (ttail et) => [|[]].
Qed.

Lemma ttail_etrace et : ttail (etrace et) = etail et.
Proof.
rewrite /etail /etrace /etrace_perm /ttail proper_permt.
case: (even_trace et); first by rewrite !permt_id.
by case: et => [|[] ?] //=; rewrite -2![permt _ _]map_comp; apply: eq_map; case.
Qed.

Lemma even_etrace et : even_trace (etrace et).
Proof. by rewrite /even_trace ttail_etrace even_etail. Qed.

Lemma compose_permt g g' et : {h | permt h et = permt g (permt g' et)}.
Proof.
have inj_gg': injective (g \o g') by apply: inj_comp; apply: permc_inj.
have [|h Dh] := color_inj_permc inj_gg'; first by rewrite /= !permc0.
by rewrite -[permt g _]map_comp; exists h; apply/esym/eq_map.
Qed.

Lemma etail_perm et : proper_trace et -> {g | permt g et = Color1 :: etail et}.
Proof.
rewrite -ttail_etrace /ttail /etrace; move: (etrace_perm et) => h.
rewrite -(proper_permt h) => et_ok; rewrite et_ok.
case Dhet: (permt h et) => //= [e het'] in et_ok *.
have [g Dget] := (compose_permt (edge_rot e) h et); exists g.
by rewrite {}Dget {}Dhet; case: e in et_ok *.
Qed.

Lemma etail_permt g et : etail (permt g et) = etail et.
Proof.
case et_ok: (proper_trace et); last first.
  by rewrite /etail /ttail proper_permt et_ok /= 2!permc0.
have get_ok: proper_trace (permt g et) by rewrite proper_permt.
have{et_ok get_ok} [[h Dhet] [h']] := (etail_perm et_ok, etail_perm get_ok).
have [g' <-{h'} Dg'et] := compose_permt h' g et.
have [g'' Eg''] := compose_permt g' (inv_eperm h) (permt h et).
rewrite {4}/permt (mapK (inv_permc h)) {g'}Dg'et {h}Dhet /= in Eg''.
case: Eg'' (even_etail et) (even_etail (permt g et)) => g''1 <-.
case: g'' g''1 => // _; first by rewrite permt_id.
by elim: {et}(etail et) => [|[] et IHet] //= *; rewrite IHet.
Qed.

(* Perimeter-trace equations. *)

Lemma ptrace_addc c (lc : colseq) : ptrace (map (addc c) lc) = ptrace lc.
Proof.
rewrite /ptrace; case: lc => //= c' lc; elim: lc c' => //= c'' lc IHlc c'.
by rewrite (addcC c) -addcA addKc IHlc.
Qed.

Lemma ptrace_permt g lc : ptrace (permt g lc) = permt g (ptrace lc).
Proof.
rewrite /ptrace; case: lc => //= c lc; elim: lc c => //= c' lc IHlc c.
by rewrite IHlc permc_addc.
Qed.

Lemma eptrace_inj lc f : injective f -> eptrace (map f lc) = eptrace lc.
Proof.
move=> injf; rewrite /eptrace -(ptrace_addc (f Color0)) -map_comp.
have injf': injective (addc (f Color0) \o f) := inj_comp (addcI _) injf.
have [|g /eq_map->] := color_inj_permc injf'; first by rewrite /= addcc.
by rewrite ptrace_permt etail_permt.
Qed.

(* Properties of the trace completion. *)

Lemma sumt_ctrace et : sumt (ctrace et) = Color0.
Proof.
rewrite /ctrace -(add0c (sumt et)).
elim: et Color0 => [|e et IHet] c /=; first by rewrite 2!addc0.
by rewrite addcA IHet (addcC c e) addKc.
Qed.

Lemma memc0_ctrace et :
  (Color0 \in ctrace et) = (sumt et == Color0) || (Color0 \in et).
Proof. by rewrite mem_rcons eq_sym. Qed.

Lemma proper_ctrace et : proper_trace (ctrace et) = proper_trace et.
Proof. by case: et => [|[]]. Qed.

Lemma sumt_permt g et : sumt (permt g et) = g (sumt et).
Proof. by elim: et => /= [|e et ->]; rewrite (permc0, permc_addc). Qed.

Lemma ctrace_permt g et : ctrace (permt g et) = permt g (ctrace et).
Proof. by rewrite /ctrace sumt_permt -map_rcons. Qed.

Lemma even_ctrace et : even_trace (ctrace et) = even_trace et.
Proof.
case: et => // e et; rewrite /ctrace /even_trace /ttail /proper_trace /=.
case: ifP => //= _; move Dg: (edge_rot e) => g.
have{Dg}: cbit1 (g e) = false by rewrite -Dg; case e.
elim: et e => [|e' et IHet] e /= ge1; first by rewrite addc0; case: (g e) ge1.
by case Dge': (g e'); rewrite //= addcA IHet // permc_addc cbit1_addc ge1 Dge'.
Qed.

Lemma ctrace_inj : injective ctrace.
Proof.
move=> et0 et0'; rewrite /ctrace; move: {-2}et0 {-2}et0'.
by elim=> [|c et IHet] [|c' et'] //; [case et' | case et | case=> -> /IHet->].
Qed.

(* Properties of the full (cyclic) trace. *)

Lemma trace_permt g lc : trace (permt g lc) = permt g (trace lc).
Proof. by case: lc => // c lc; rewrite /trace -ctrace_permt -ptrace_permt. Qed.

Lemma size_trace lc : size (trace lc) = size lc.
Proof.
by case: lc => // *; rewrite /trace /ctrace /ptrace /= size_rcons size_pairmap.
Qed.

Lemma trace_untrace c0 et : sumt et = Color0 -> trace (untrace c0 et) = et.
Proof.
case: et => // e1 et sum_et; rewrite /untrace /= /ptrace /= (scanlK addKc).
rewrite /ctrace lastI -[last e1 et]add0c -{}sum_et; congr (rcons _ _).
by elim: et e1 => [|e2 et IHet] e1 /=; rewrite -addcA ?addcc ?IHet.
Qed.

Lemma sumt_trace lc : sumt (trace lc) = Color0.
Proof. by case: lc => // c lc; rewrite sumt_ctrace. Qed.

Lemma untrace_trace c0 lc : untrace c0 (trace (c0 :: lc)) = c0 :: lc.
Proof. by rewrite /untrace /ctrace belast_rcons /= addc0 (pairmapK addKc). Qed.

Lemma trace_addc c lc : trace (map (addc c) lc) = trace lc.
Proof.
by case: lc => //= c0 lc; rewrite [pairmap _ _ _](ptrace_addc _ (_ :: _)).
Qed.

Lemma trace_cons c lc : trace (c :: lc) = pairmap addc c (rcons lc c).
Proof.
rewrite /trace /ptrace /ctrace /= -[sumt _](addKc c).
elim: lc {-2 6}c => [|c2 lc IHlc] c1 /=; first by rewrite addc0 addcC.
by rewrite -!addcA addKc IHlc.
Qed.

Lemma trace_rcons c (lc : colseq) :
  trace (rcons lc c) = if trace (c :: lc) is e :: et then rcons et e else lc.
Proof.
case: lc => // c1 lc; rewrite rcons_cons !trace_cons /=.
by elim: lc {1 3}c1 => //= c3 lc IHlc c2; rewrite IHlc.
Qed.

Lemma urtrace_trace (lc : colseq) : urtrace (rot 1 lc) = trace lc.
Proof.
case: lc => [|c1 [|c2 lc]]; rewrite /urtrace /rot //= ?addcc // last_cat /=.
rewrite /ctrace /= cats1 -addcA; congr (_ :: _).
elim: lc c2 => [|c3 lc IHlc] c2 /=; first by rewrite addc0 addcC.
by rewrite -addcA addKc -IHlc.
Qed.

Lemma urtrace_rot (lc : colseq) : urtrace (rot 1 lc) = rot 1 (urtrace lc).
Proof.
case: lc => [|c1 [|c2 lc]]; rewrite /urtrace /rot //= last_cat /= !cats1.
by congr (_ :: _); elim: lc c2 => //= c3 lc IHlc c2; rewrite IHlc.
Qed.

Lemma trace_rot n (lc : colseq) : trace (rot n lc) = rot n (trace lc).
Proof.
elim: n => [|n IHn]; first by rewrite !rot0.
have [le_le_c | lt_n_le] := leqP (size lc) n.
  by rewrite !rot_oversize ?size_trace // ltnW.
by rewrite -add1n !rotD ?size_trace // -IHn -!urtrace_trace -urtrace_rot.
Qed.

Lemma trace_rev (lc : colseq) : trace (rev lc) = rot 1 (rev (trace lc)).
Proof.
case: lc => // c0 lc; rewrite -!urtrace_trace !urtrace_rot; congr (rot 1 _).
elim/last_ind: lc => // lc c /(congr1 behead).
case/lastP: lc => [|lc c']; first by rewrite /urtrace /= (addcC c).
rewrite -!rcons_cons !rev_rcons -2!rot1_cons !urtrace_rot -urtrace_rot.
do 2!rewrite /urtrace /= ?rot1_cons /=; rewrite !rev_rcons /= => <-.
by rewrite rev_cons cats1 !last_rcons !(addcC c).
Qed.
