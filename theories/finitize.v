(* (c) Copyright 2006-2018 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrfun ssrbool eqtype ssrnat seq choice path ssralg ssrint.
From fourcolor
Require Import real realplane realsyntax realprop.
From fourcolor
Require Import grid approx.

(******************************************************************************)
(*   We use a special case of the compactness theorem for predicate logic to  *)
(* extend the Four Color Theorem from finite to arbitrary map. We can         *)
(* dispense with the full axiom of choice as maps have only countably many    *)
(* regions because of the local compactness of the plane.                     *)
(*   Given a natural integer nc such that all finite maps are nc-colorable    *)
(* and a (possibly infinite) simple plane map m0, we construct an nc-coloring *)
(* of m0 by defining (locally) the following:                                 *)
(*       [map z1 z2 | E] == the map defined by relation E of z1 and z2.       *)
(*          eq_map m1 m2 <-> maps m1 and m2 coincide (relate the same points) *)
(*     'z_i, std_point i == the i'th scaled grid point (in a standard, fixed  *)
(*                          enumeration).                                     *)
(*             in_pmap n == the union of the regions of m0 containing one of  *)
(*                          the first n scaled grid points.                   *)
(*              pmap n k == the restriction of map k to in_pmap n.            *)
(*      eq_pmap n k1 k2 <-> maps k1 and k2 coincide on in_pmap n.             *)
(*        subcoloring k <-> k is an nc-coloring consistent with m0, i.e., k   *)
(*                          does not relate points in adjacent regions of m0. *)
(*        pcoloring n k <-> k is a subcoloring covering at least in_pmap n.   *)
(*       extensible n k <-> the coloring of in_pmap n induced by k extends to *)
(*                          nc-colorings of in_pmap n' for any n'.            *)
(*     fin_color_map n g == the (plain) map whose (at most) n regions are     *)
(*                          the preimages by g : point R -> R of the integers *)
(*                          i in R, 0 <= i < n.                               *)
(*  prefix_coloring n k <-> k is an extensible coloring of pmap n m0 (this    *)
(*                          implies pcoloring n k) that in addition assigns a *)
(*                          lexicographically minimal sequence of colors to   *)
(*                          the n first scaled grid points, when colors       *)
(*                          (i.e., regions) of a pcoloring are ordered by     *)
(*                          their index in some enumeration (recall a         *)
(*                          pcoloring has at most nc regions), chosen to      *)
(*                          yield the smallest grid point color sequence.     *)
(*          minimal n k <-> the minimality property of a prefix_coloring n k. *)
(*                          This is stated in an equivalent form that avoids  *)
(*                          constructing color sequences: that any extensible *)
(*                          coloring of pmap i+1 m0, i < n, which coincides   *)
(*                          with k on all 'z_j, j < i, can only relate 'z_i   *)
(*                          to a 'z_j with j no smaller than the smallest j0  *)
(*                          for which k 'z_j0 'z_i.                           *)
(*          is_prefix k <-> k is a prefix_coloring for some n.                *)
(*        limit_coloring == the union of the inclusion chain of prefix        *)
(*                          colorings, which we show is a (lexicographically  *)
(*                          minimal) nc-coloring of m0.                       *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section FinitizeMap.

Variable R : Real.model.

Import RealPlaneCoercions.
Local Notation Rstruct := (Real.model_structure R) (only parsing).
Local Notation point := (point Rstruct).
Local Notation region := (region Rstruct).
Local Notation map := (map Rstruct).

(* Classical reasoning helper lemmas. *)

Let Rclassic : excluded_middle := reals_classic R.

Let RcontraR (P Q : Prop) : (~ P -> Q) -> ~ Q -> P.
Proof. by case: (Rclassic P) => // notP /(_ notP). Qed.

Let Rwlog (P Q : Prop) : (~ Q -> P) -> (Q -> P) -> P.
Proof. by move=> notQ_P Q_P; case: (Rclassic Q) => [/Q_P | /notQ_P]. Qed.

(* Local notational conventions. *)

Implicit Types (m k : map) (z t : point).

Local Notation "[ 'map' z1 z2 | E ]" := ((fun z1 z2 : point => E) : map)
  (z1, z2 at level 0, format "[ 'map'  z1  z2  |  E ]").

(* Derived map transitivity and equivalence lemmas. *)

Section MapTrans.

Variable m : map.
Hypothesis mP : plain_map m.
Let mS := map_sym mP.

Lemma map_transl {z1 z2}: implies (m z1 z2) (forall z, m z1 z <-> m z2 z).
Proof. by split=> mz12 z; split; apply/(map_trans mP); first apply/mS. Qed.

Lemma map_transr {z1 z2}: implies (m z1 z2) (forall z, m z z1 <-> m z z2).
Proof. by split=> /map_transl-mz12 z; split=> /mS/mz12/mS. Qed.

Lemma map_cover {z1 z2}: implies (m z1 z2) (cover m z1 /\ cover m z2).
Proof.
by split=> mz12; split; [apply/(map_transr mz12) | apply/(map_transl mz12)].
Qed.

End MapTrans.

(* A canonical enumeration of grid points. *)

Definition std_point i : point :=
  let: (s, p) := odflt (0%N, 0%R : gpoint) (unpickle i) in scale_point R s p.

Local Notation "'z_ i" := (std_point i) (at level 8, format "''z_' i").

(* An alternative characterization of at_most_regions not used in the current *)
(* proof: finite maps as the same-image relation for a partial function with  *)
(* a finite codomain - specifically, the n first naturals in R. Note that we  *)
(* can't use funtions to nat, because we only assume excluded middle in Prop. *)
(* (This is a holdover from the original proof in Coq version 7, where this   *)
(* would have been inconsistent because Set was impredicative in Coq v7.      *)

Definition eq_map m1 m2 := forall z t, m1 z t <-> m2 z t.

Definition fin_color_map n (g : point -> R) :=
  [map z t | exists2 i, i < n & (g z == g t == i%:R)%Rval].

Lemma at_most_regionsP n m :
  plain_map m /\ at_most_regions n m <-> exists g, eq_map m (fin_color_map n g).
Proof.
have RleqP i j : reflect (i%:R <= j%:R)%Rval (i <= j) := @intR_leP R i j.
elim: n m => [|n IHn] m; do [split=> [[mP [f fP]] | [g gP]]; last first].
- by split; [split=> t | exists (fun=> 'z_0)] => z /gP[].
- by exists (fun=> 0%Rval) => z t; split=> [/(map_cover mP)[/fP[i /ltP]] | []].
- have mP: plain_map m.
    split=> z t /gP[i lti [Dgz Di]]; first by apply/gP; exists i; rewrite ?Dgz.
    by move=> u /gP[_ _ [Dgu _]]; apply/gP; exists i; rewrite -?Dgu.
  have [_ [|_ [f fP]]] := IHn (fin_color_map n g); first by exists g.
  have [zn znP]: (exists zn, forall z, g z == n%:R -> g zn == n%:R)%Rval.
    have [[zn]|] := Rclassic (exists z, g z == n%:R)%Rval; first by exists zn.
    by move=> g'n; exists 'z_0 => z gz_n; case: g'n; exists z.
  split=> //; exists [eta f with n |-> zn] => z /gP[i]; rewrite ltnS leq_eqVlt.
  case/predU1P=> [-> | lt_i_n] /= [_ Dgz].
    by exists n; [apply/ltP | apply/gP; exists n; rewrite // eqxx Dgz (znP z)].
  have [|j /ltP-lt_j_n [i1 _ [Dfj Di1]]] := fP z; first by exists i.    
  by exists j; [apply/ltP/leqW | apply/gP; exists i; rewrite ?ltn_eqF ?leqW].
have [[|g gP _]] := IHn [map z t | m z t /\ ~ m z (f n)].
  split; first split=> z t [/(map_sym mP)mtz m'zn] => [|u [mtu m'tn]].
  - by rewrite (map_transl mP mtz (f n)).      
  - by rewrite -(map_transl mP mtz).
  exists f => z [/fP[i /ltP-le_i_n m_iz] m'zn].
  exists i; [apply/ltP | by split=> // /(map_transl mP m_iz)].
  by rewrite ltn_neqAle; case: eqP m'zn => // <- []; apply/(map_sym mP).
pose h z := (IF m z (f n) then n%:R else IF m z z then g z else n.+1%:R)%Rval.
exists h => z t; split=> [mzt | [i le_i_n [Dhz Dht]]].
  have [m_z m_t] := map_cover mP mzt.
  have [mzn | m'zn] := Rclassic (m z (f n)).
    by exists n; rewrite // /h !IFR_then // -(map_transl mP mzt).
  have [[//| i /leqW-lt_i_n1 Dgzt_i] _] := gP z t; exists i => //.
  by rewrite /h -(map_transl mP mzt) IFR_else 1?IFR_then // IFR_else ?IFR_then.
generally have m_t, m_z: z Dhz / m z z; last have{m_t} m_t: m t t by apply: m_t.
  have: (h z < n.+1%:R)%Rval by rewrite Dhz Dht; apply/RleqP; rewrite -ltnNge.
  by apply: RcontraR => m'z; rewrite /h !IFR_else // => /(map_cover mP)[].
generally have m_tnP, m_zn: z Dhz m_z / m z (f n) <-> i == n.
  split=> [m_zn | /eqP-Di].
    by rewrite eqn_leq -ltnS le_i_n; apply/RleqP; rewrite -Dht -Dhz /h IFR_then.
  have: ~ (h z < n%:R)%Rval by case; rewrite Dhz Dht Di.
  apply: RcontraR => m'zn; rewrite /h IFR_else // IFR_then //.
  have [[//|j lt_j_n [_ Dj]] _] := gP z z; rewrite {}Dj.
  by apply/RleqP; rewrite -ltnNge.
have /orP[Di | lt_i_n]: (i == n) || (i < n) by rewrite -leq_eqVlt.
  by rewrite (map_transr mP (_ : m t (f n))) (m_zn, m_tnP).
have [_ [|//]] := gP z t; exists i => //; move: (Dhz) Dht.
by rewrite /h !m_tnP ?ltn_eqF //; do 2!rewrite IFR_else // IFR_then //.
Qed.

(* Section assumption context. *)

Variable nc : nat.
Hypothesis fin_colorable : forall m, finite_simple_map m -> colorable_with nc m.

Variable m0 : map.
Hypothesis m0P : simple_map m0.

(* Limit construction of the full (infinite) map coloring. *)

Definition in_pmap n : region := fun z => exists2 i, i < n & m0 z 'z_i.

Definition pmap n m := [map z1 z2 | [/\ in_pmap n z1, in_pmap n z2 & m z1 z2]].

Definition eq_pmap n k k' :=
  forall z1 z2, in_pmap n z1 -> in_pmap n z2 -> k z1 z2 <-> k' z1 z2.

Record subcoloring k : Prop := SubColoring {
  subcoloring_plain :> plain_map k;
  subcoloring_adj z1 z2 : adjacent m0 z1 z2 -> ~ k z1 z2;
  subcoloring_size : at_most_regions nc k
}.

Definition pcoloring n k := subcoloring k /\ submap (pmap n m0) k.

Definition extensible n0 k0 :=
  forall n, exists2 k, pcoloring n k & eq_pmap n0 k0 k.

Let minimal n k0 :=
  forall i j k, i < n ->
    eq_pmap i k0 k -> pmap i.+1 k 'z_j 'z_i -> extensible i.+1 k ->
  exists2 j0, j0 <= j & k0 'z_j0 'z_i.

Definition prefix_coloring n k :=
  [/\ submap k (pmap n k), extensible n k & minimal n k].

Definition is_prefix k := exists n, prefix_coloring n k.

Definition limit_coloring := [map z1 z2 | exists2 k, is_prefix k & k z1 z2].

(* Standard point properties. *)

Lemma has_std_point z : cover m0 z -> exists i, m0 z 'z_i.
Proof.
move=> m0z; have [rr rrz m0rr] := simple_map_open m0P m0z.
have [b [p p_z /insetW-b_p] rr_b] := approx_rect rrz.
set s := _.1 in p_z; exists (pickle (s, p)); rewrite /std_point pickleK /=.
exact/m0rr/rr_b/mem_approx_scale.
Qed.

Lemma pmap_std n1 n2 i : i < n1 -> in_pmap n2 'z_i -> in_pmap n1 'z_i.
Proof. by move=> lt_i_n1 [_ _ /(map_cover m0P)[m0i _]]; exists i. Qed.

(* Partial map cover properties. *)

Lemma in_pmap_le n1 n2 : n1 <= n2 -> subregion (in_pmap n1) (in_pmap n2).
Proof. by move=> le_n12 z [i]; exists i; first apply: leq_trans le_n12. Qed.

Lemma in_pmap_trans n z : in_pmap n z -> subregion (m0 z) (in_pmap n).
Proof.
by case=> i ltin m0zi t m0zt; exists i => //; apply/(map_transl m0P m0zt).
Qed.

Lemma cover_pmap n z : cover (pmap n m0) z <-> in_pmap n z.
Proof. by split=> [[] // | n_z]; have [_ _ /(map_cover m0P)[m0z _]] := n_z. Qed.

Lemma in_pmapP n z : in_pmap n z -> exists2 i, i < n & pmap n m0 z 'z_i.
Proof.
move=> n_z; have [i lt_i_n m0zi] := n_z; suffices: in_pmap n 'z_i by exists i.
exact: in_pmap_trans n_z _ m0zi.
Qed.

(* Partial map equality. *)

Lemma eq_pmap_sym n k k' : eq_pmap n k k' -> eq_pmap n k' k.
Proof. by move=> Ekk'; split=> /Ekk'; apply. Qed.

Lemma eq_pmap_trans n k1 k2 k3 :
  eq_pmap n k1 k2 -> eq_pmap n k2 k3 -> eq_pmap n k1 k3.
Proof. by move=> Ek12 Ek23; split=> [/Ek12/Ek23 | /Ek23/Ek12]; apply. Qed.

Lemma eq_map_pmap n k : eq_pmap n k (pmap n k). Proof. by split=> [|[]]. Qed.

Lemma sub_pmap_pmap n k : submap (pmap n k) (pmap n (pmap n k)).
Proof. by move=> z1 z2 []. Qed.

Lemma eq_pmap_le {n1 n2 k k'} :
  n1 <= n2 -> implies (eq_pmap n2 k k') (eq_pmap n1 k k').
Proof.
by move/in_pmap_le=> n2_n1; split=> Ekk' z1 z2 /n2_n1-n2z1 /n2_n1; apply: Ekk'.
Qed.

(* Partial map properties. *)

Lemma pmap_sub n m : submap (pmap n m) m. Proof. by move=> z1 z2 []. Qed.

Lemma pmap_le n1 n2 : n1 <= n2 -> forall m, submap (pmap n1 m) (pmap n2 m).
Proof. by move/in_pmap_le=> n2n1 m z1 z2 [/n2n1-n2z1 /n2n1-n2z2]. Qed.

Lemma pmap_plain n m : plain_map m -> plain_map (pmap n m).
Proof.
move=> mP; split=> z1 z2 [n_z1 _ /(map_sym mP)m_z21] //.
by move=> z3 [_ n_z3 /(map_transl mP m_z21)m_z13].
Qed.

Lemma pmap_finite n : finite_simple_map (pmap n m0).
Proof.
split; last first.
  exists n, std_point => z [n_z [i lt_i_n m0zi] _]; exists i; first exact/ltP.
  by split; [apply/(in_pmap_trans n_z) | | apply/(map_sym m0P)].
split; first exact: (pmap_plain n m0P).
  move=> z1 z2 [n_z1 n_z2 m0z12].
  have [r r_z2 m0_r] := simple_map_open m0P m0z12.
  by exists r => // z /m0_r-m0z1z; split=> //; apply: in_pmap_trans m0z1z.
move=> z r1 r2 r1P r2P r12_nz [z1 [r1z1 [n_z _ m0zz1]]] [z2 [r2z2 [_ _ m0zz2]]].
have []: meet r1 (m0 z) /\ meet r2 (m0 z) by split; [exists z1 | exists z2].
apply: simple_map_connected => // t m0zt.
by have n_t: in_pmap n t := in_pmap_trans n_z m0zt; apply/r12_nz.
Qed.

Lemma size_pmap n k :
  plain_map k -> at_most_regions nc k -> at_most_regions nc (pmap n k).
Proof.
set kn := pmap n k => kP [f f_k].
pose kfn i := intersect (k (f i)) (in_pmap n).
suffices [g g_k]: exists g, forall i, i < nc -> subregion (kfn i) (kn (g i)).
  exists g => z [n_z _ /f_k[i /ltP-lt_i_nc kiz]].
  by exists i; [apply/ltP | apply/g_k].
elim: nc => [|i [g g_k]]; first by exists f.
have [[t [k_fi_t n_t]] | kfn'i] := Rclassic (nonempty (kfn i)).
  exists [eta g with i |-> t] => j /=; rewrite ltnS.
  by case: (ltngtP j) => [/g_k||->] // _ z [/(map_transl kP k_fi_t)].
exists g => j; rewrite ltnS leq_eqVlt => /predU1P[->|/g_k//] z kfn_iz.
by case: kfn'i; exists z.
Qed.

(* Partial map coloring. *)

Lemma pmap_subcoloring n k : subcoloring k -> subcoloring (pmap n k).
Proof.
case=> kP adj'k /(size_pmap n kP)-le_kn_nc; have knP := pmap_plain n kP.
by split=> // z1 z2 /adj'k-not_kz12 /pmap_sub.
Qed.

Lemma pcoloring_exists n : exists k, pcoloring n k.
Proof.
have [k [kP n_k k_n adj'k] nc_k] := fin_colorable (pmap_finite n).
have clos_n z t: in_pmap n z -> closure (m0 z) t -> closure (pmap n m0 z) t.
  move=> n_z m0zt r rP r_t; have [u [m0zu r_u]] := m0zt r rP r_t.
  by exists u; do !split => //; apply: in_pmap_trans m0zu.
exists k; do 2![split=> //]=> z1 z2 [m0'z12 [z [[f fP] [z1z z2z]]] kz12].
have [/n_k[n_z1 _ _] /n_k[n_z2 _ _]] := map_cover kP kz12.
apply: adj'k kz12; split=> [/pmap_sub//|]; exists z.
split; [exists f => t [[_ n_t m0t] m0tz] | by split; apply/clos_n].
have /fP[i lti2 [m0it m0iz]]: cover (corner_map m0 z) t.
  by split=> // r rP /(m0tz r rP)[u [/pmap_sub-m0tu r_u]]; exists u.
have n_i: in_pmap n (f i) by apply/(in_pmap_trans n_t)/(map_sym m0P).
by exists i => //; split=> //; apply: clos_n.
Qed.

Lemma pcoloring_le n1 n2 k : n1 <= n2 -> pcoloring n2 k -> pcoloring n1 k.
Proof.
by move=> len12 [k_n2 n_k]; split=> // z1 z2 n1z12; apply/n_k/(pmap_le len12).
Qed.

Lemma pmap_extensible n1 n2 k :
  n1 <= n2 -> extensible n2 k -> extensible n1 (pmap n1 k).
Proof.
move=> le_n12 ext_k n; have [k' k'P /(eq_pmap_le le_n12)Ekk'] := ext_k n.
by exists k' => //; apply/(eq_pmap_trans _ Ekk')/eq_pmap_sym/eq_map_pmap.
Qed.

(* Properties of limit coloring prefixes. *)

Lemma prefix_pcoloring n k : prefix_coloring n k -> pcoloring n k.
Proof.
case=> n_k /(_ n)[k' [[k'P adj'k' /(size_pmap n k'P)[f k'f_nk']] k'nm0] Ekk'] _.
have k'_k: submap k k' by move=> z1 z2 /n_k[nz1 nz2 kz12]; apply/Ekk'.
split=> [|z1 z2 [n_z1 n_z2 m0k12]]; last exact/Ekk'/k'nm0.
split=> [|z1 z2 adj_z12 /k'_k/adj'k'[]//|].
  split=> z1 z2 /n_k[nz1 nz2 kz12] => [|z3 /n_k[_ nz3 /Ekk'-k'z23]].
    exact/Ekk'/(map_sym k'P)/Ekk'.
  exact/Ekk'/(map_trans k'P _ (k'z23 nz2 nz3))/Ekk'.
exists f => z /n_k[nz _ /k'_k-k'z].
by have [//| i lt_i_nc [nfi _ k'fiz]] := k'f_nk' z; exists i; last apply/Ekk'.
Qed.

Lemma prefix_coloring_exists n : exists k, prefix_coloring n k.
Proof.
elim: n => /= [|n [k0 [n_k0 ext_k0 min_k0]]].
  exists [map z1 z2 | False]; split=> // n.
  by have [k [kP k_n]] := pcoloring_exists n; exists k => // z1 z2 [].
set n1 := n.+1; have le_nn1: n <= n1 := leqnSn n.
without loss n1_n: / in_pmap n1 'z_n.
  apply: Rwlog => n1'n; have En1n z: in_pmap n1 z -> in_pmap n z.
    by case/in_pmapP=> i; rewrite leq_eqVlt => /predU1P[[->]|?] [] //; exists i.
  exists k0; split=> [z1 z2 /n_k0/(pmap_le le_nn1)// | i | n' i k'].
    have [k kP Ek0k] := ext_k0 i.
    by exists k => // z1 z2 /En1n-n_z1 /En1n-n_z2; apply: Ek0k.
  by rewrite leq_eqVlt => /predU1P[[->] _ [_ /cover_pmap[]] //|]; apply: min_k0.
pose ext n0 j k := [/\ pcoloring n0 k, eq_pmap n k0 k & pmap n1 k 'z_j 'z_n].
pose limit_min j0 := exists2 n0, n < n0 & forall j k, ext n0 j k -> j0 <= j.
have{ext_k0}: ~ limit_min n1.
  case=> n0 lt_nn0 min_n0; have [k [kP k_n0] eq_k0k] := ext_k0 n0.
  case/negP: (ltnn n); apply: (min_n0 n k).
  by do 2!split=> //; apply/k_n0/cover_pmap/(pmap_std lt_nn0 n1_n).
elim: {1 3}n1 (leqnn n1) => [_ []|j0 IHj0 le_j0n min'j1]; first by exists n1.
wlog{IHj0} [n0 lt_nn0 min_j0]: / limit_min j0 by apply: Rwlog; apply/IHj0/ltnW.
have{min'j1} ext0P n': n0 <= n' -> exists2 k, pcoloring n' k & ext n0 j0 k.
  move=> le_n0n'; have lt_nn': n < n' := leq_trans lt_nn0 le_n0n'.
  apply: RcontraR min'j1 => ext'n'; exists n' => // j k [kP Ek0k] k_jn.
  have kPn0: pcoloring n0 k := pcoloring_le le_n0n' kP.
  rewrite ltn_neqAle (min_j0 j k) //.
  by apply: RcontraR ext'n'; case: eqP => // ->; exists k.
have [k1 _ Dk1] := ext0P n0 (leqnn n0); pose k2 := pmap n.+1 k1.
have Ek12: eq_pmap n.+1 k1 k2 by apply: eq_map_pmap.
have m1P z: in_pmap n.+1 z -> exists2 j, j <= n & pmap n0 m0 z 'z_j.
  by case/in_pmapP=> j le_jn /(pmap_le lt_nn0); exists j.
have n1j0 : in_pmap n1 'z_j0 by have [_ _ []] := Dk1.
exists k2; split; first exact: sub_pmap_pmap; last first.
  have [_ Ek01 k2_j0n] := Dk1 => i j k le_i_n Ek2k i1k_ji ext_k.
  have Ek02: eq_pmap n k0 k2 := eq_pmap_trans Ek01 (eq_pmap_le le_nn1 Ek12).
  have Ek0k: eq_pmap i k0 k by apply: eq_pmap_trans (eq_pmap_le _ Ek02) Ek2k.
  have [Di | lt_i_n]: i = n \/ i < n by apply/predU1P; rewrite -leq_eqVlt.
    rewrite Di in i1k_ji Ek0k ext_k *; exists j0 => //.
    have [[k' k'P Ekk'] [n1j _ k_ji]] := (ext_k n0, i1k_ji).
    apply: (min_j0 j k'); split=> //; last by split; last apply/Ekk'.
    exact: eq_pmap_trans Ek0k (eq_pmap_le le_nn1 Ekk').
  by case: (min_k0 i j k) => // j1 le_j1j /n_k0[]; exists j1; last apply/Ek02.
move=> n'; have [|k3 k3P Dk3] := ext0P (maxn n0 n'); first exact: leq_maxl.
suffices{k2 Ek12 k3P} Ek13: eq_pmap n.+1 k1 k3.
  have Ek23: eq_pmap n.+1 k2 k3 := eq_pmap_trans (eq_pmap_sym Ek12) Ek13.
  by exists k3; first apply/(pcoloring_le _ k3P)/leq_maxr.
move=> z1 z2 /m1P[i1 le_i1n n0iz1] /m1P[i2 le_i2n n0iz2].
have [[_ n0i1 _] [_ n0i2 _]] := (n0iz1, n0iz2).
without loss suffices ext_subpmap: k1 k3 Dk1 Dk3 / k1 z1 z2 -> k3 z1 z2.
  by split; apply: ext_subpmap.
have{Dk1} [[k1P k1n0] Ek01 [_ _ k1j0n]] := Dk1.
have{Dk3} [[k3P k3n0] Ek03 [_ _ k3j0n]] := Dk3.
suffices{z1 z2 n0iz1 n0iz2} k13i: k1 'z_i1 'z_i2 -> k3 'z_i1 'z_i2.
  have [/k1n0-k1iz1 /k1n0-k1iz2] := (n0iz1, n0iz2).
  have [/k3n0-k3iz1 /k3n0-k3iz2] := (n0iz1, n0iz2).
  move/(map_transl k1P k1iz1)/(map_transr k1P k1iz2).
  by move/k13i/(map_transl k3P k3iz1)/(map_transr k3P k3iz2).
without loss{k3n0} lt_i12: i1 le_i1n n0i1 i2 le_i2n n0i2 / i1 < i2.
  move=> IHi; have [lt_i12 | lt_i21 | -> _] := ltngtP i1 i2; first exact: IHi.
    by move/(map_sym k1P)/IHi/(map_sym k3P); apply.
  exact/k3n0/cover_pmap.
have lt_i1n: i1 < n := leq_trans lt_i12 le_i2n.
have n_i1: in_pmap n 'z_i1 := pmap_std lt_i1n n0i1.
have Ek13: eq_pmap n k1 k3 := eq_pmap_trans (eq_pmap_sym Ek01) Ek03.
have [-> k1i1n | lti2n]: i2 = n \/ i2 < n by apply/predU1P; rewrite -leq_eqVlt.
  apply/(map_transr k3P k3j0n)/Ek13/(map_transr k1P k1j0n)=> //.
  apply/(pmap_std _ n1j0)/(leq_ltn_trans _ lt_i1n)/(min_j0 i1 k1).
  by do 2!split=> //; apply: pmap_std n_i1. 
by move=> k1z12; apply/Ek13=> //; apply: pmap_std n0i2.
Qed.

Lemma prefix_coloring_le n1 n2 k1 k2 :
  n1 <= n2 -> prefix_coloring n1 k1 -> prefix_coloring n2 k2 -> submap k1 k2.
Proof.
move=> le_n12 k1pre k2pre; have [n1k1 _ _] := k1pre.
without loss{n2 le_n12 k2pre} k2pre: k2 / prefix_coloring n1 k2.
  have [[n2k2 k2_ext k2_min] [k2P _]] := (k2pre, prefix_pcoloring k2pre).
  move=> IHn2 _ _ /(IHn2 (pmap n1 k2))[] //.
  split; [exact: sub_pmap_pmap | exact: pmap_extensible k2_ext |].
  move=> i j k lt_i_n1 Ek2k i1k_ji k_ext.
  case: (k2_min i j k) => // [||j0 le_j0j k2j0i]; first exact: leq_trans le_n12.
    exact/(eq_pmap_trans _ Ek2k)/(eq_pmap_le (ltnW lt_i_n1))/eq_map_pmap.
  have [i1j i1i _] := i1k_ji; have n1i := pmap_std lt_i_n1 i1i.
  have [/n2k2[n2j0 _ _] k2i] := map_cover k2P k2j0i.
  have [le_i_j | lt_j_i] := leqP i j; first by exists i.
  have lt_j0_n1: j0 < n1 := leq_ltn_trans le_j0j (ltn_trans lt_j_i lt_i_n1).
  by exists j0 => //; split=> //; apply: pmap_std lt_j0_n1 n2j0.
suffices Ek12: eq_pmap n1 k1 k2 by move=> z1 z2 /n1k1[nz1 nz2 k1z]; apply/Ek12.
elim: {-2}n1 (leqnn n1) => /= [|n IHn] lt_nn1 z1 z2; first by case.
have m1P z: in_pmap n.+1 z -> exists2 i, i <= n & pmap n1 m0 z 'z_i.
  by case/in_pmapP=> i le_i_n n1zi; exists i; last apply: pmap_le n1zi.
move/(_ (ltnW lt_nn1)) in IHn => /m1P[i1 le_i1n n1iz1] /m1P[i2 le_i2n n1iz2].
without loss suffices{n1k1} IHk: k1 k2 k1pre k2pre IHn / k1 z1 z2 -> k2 z1 z2.
  by split; apply: IHk => //; apply/eq_pmap_sym.
have [[k1P k1n1] [_ n1i1 _]] := (prefix_pcoloring k1pre, n1iz1).
have [[k2P k2n1] [_ n1i2 _]] := (prefix_pcoloring k2pre, n1iz2).
suffices{z1 n1iz1 z2 n1iz2} k12i: k1 'z_i1 'z_i2 -> k2 'z_i1 'z_i2.
  have [/k1n1-k1iz1 /k1n1-k1iz2] := (n1iz1, n1iz2).
  have [/k2n1-k2iz1 /k2n1-k2iz2] := (n1iz1, n1iz2).
  move/(map_transl k1P k1iz1)/(map_transr k1P k1iz2).
  by move/k12i/(map_transl k2P k2iz1)/(map_transr k2P k2iz2).
without loss lt_i12: i1 i2 le_i1n le_i2n n1i1 n1i2 / i1 < i2.
  move=> IHi; have [lt_i12 | lt_i21 | -> _] := ltngtP i1 i2; first exact: IHi.
    by move/(map_sym k1P)/IHi/(map_sym k2P); apply.
  exact/k2n1/cover_pmap.
have [lt_i1n1 lt_i2n1]: i1 < n1 /\ i2 < n1 by split; apply: leq_trans lt_nn1.
have lt_i1n: i1 < n by apply: leq_trans lt_i12 le_i2n.
case: (ltngtP i2) le_i2n => // [lt12n|Di2] _.
  by move/IHn; apply; [apply: pmap_std n1i1 | apply: pmap_std n1i2].
rewrite {i2}Di2 in n1i2 lt_i12 {le_i1n lt_i2n1} * => k1i1n.
elim: {1}n i1 lt_i12 => // n3 IHn3 i1 lt_i1n3 in lt_i1n {lt_i1n1} n1i1 k1i1n *.
have [[n1k1 k1ext k1min] [n1k2 k2ext k2min]] := (k1pre, k2pre).
have [n'_i1 n'_n] := (pmap_std (leqW lt_i1n) n1i1, pmap_std (ltnSn n) n1i2).
have /(k2min n i1)[//|//|//|i3] := pmap_extensible lt_nn1 k1ext.
  exact/(eq_pmap_trans (eq_pmap_sym IHn))/(eq_pmap_le (leqnSn n))/eq_map_pmap.
rewrite leq_eqVlt => /predU1P[-> // | lt_i31] k2i3n.
have lt_i3n: i3 < n by apply: ltn_trans lt_i1n.
have n'i3: in_pmap n.+1 'z_i3 by have /n1k2[/(pmap_std (leqW lt_i3n))] := k2i3n.
have /(k1min n i3)[//|//|//|i4 le_i43 k1i4n] := pmap_extensible lt_nn1 k2ext.
  exact/(eq_pmap_trans IHn)/(eq_pmap_le (leqnSn n))/eq_map_pmap.
have lt_i4n: i4 < n by apply: leq_trans lt_i3n.
have lt_i4n3: i4 < n3 by apply: (leq_trans (leq_ltn_trans le_i43 lt_i31)).
have n1i4: in_pmap n1 'z_i4 by case/n1k1: k1i4n.
have: k2 'z_i4 'z_n by [apply/IHn3]; apply: (map_trans k2P).
by apply/IHn/(map_transr k1P k1i4n)=> //; apply/(@pmap_std _ n1).
Qed.

(* The constructed limit is an nc-coloring of m0. *)

Lemma limit_coloring_coloring : coloring m0 limit_coloring.
Proof.
split=> [|z [k [n [n_k _ _]] /n_k[/cover_pmap[]]] //||]; last 1 first.
- by move=> z1 z2 adj_z12 [k [n /prefix_pcoloring[[_ /(_ z1 z2 adj_z12)]]]].
- split=> z1 z2 [k1 [n1 k1Pn] k1z12] => [|z3 [k3 [n3 k3Pn] k3z23]].
    have [k1P _] := prefix_pcoloring k1Pn.
    by exists k1; [exists n1 | apply/(map_sym k1P)].
  have [k kPn [k_z12 k_z23]]: exists2 k, is_prefix k & k z1 z2 /\ k z2 z3.
    case/orP: (leq_total n1 n3) => /prefix_coloring_le => [sub_k13 | sub_k31].
      by exists k3; [exists n3 | split; first apply: sub_k13 k1z12].
    by exists k1; [exists n1 | split; last apply: sub_k31 k3z23].
  have [_ /prefix_pcoloring[kP _]] := kPn.
  by exists k => //; apply/(map_trans kP k_z12).
move=> z1 z2 m0z12; have [m0z1 m0z2] := map_cover m0P m0z12.
have [[i1 m0iz1] [i2 m0iz2]] := (has_std_point m0z1, has_std_point m0z2).
have [n lt_i1n lt_i2n]: exists2 n, i1 < n & i2 < n.
  by exists (maxn i1 i2).+1; rewrite ltnS (leq_maxl, leq_maxr).
have [k kPn] := prefix_coloring_exists n; exists k; first by exists n.
by have [kP] := prefix_pcoloring kPn; apply; split; [exists i1 | exists i2 | ].
Qed.

Lemma size_limit_coloring : at_most_regions nc limit_coloring.
Proof.
pose inmf n k (f : nat -> point) := forall i, i < n -> cover k (f i).
pose injf n (k : map) f :=  forall i j, i < j -> j < n -> ~ k (f i) (f j).
pose minsize n k := exists2 f, inmf n k f & injf n k f.
without loss [f lim_f inj_limf]: / minsize nc.+1 limit_coloring.
  apply: Rwlog; move: limit_coloring => k; elim: nc => [|n IHn] nonmin_n.
    by exists std_point => z k_z; case: nonmin_n; exists (fun=> z) => [i|i []].
  without loss [f k_f inj_fk]: / minsize n.+1 k.
    apply: Rwlog => /IHn[f kf_k]; exists f => z /(kf_k z)[i /ltP/leqW/ltP].
    by exists i.
  exists f => z k_z; pose fz i := if i < n.+1 then f i else z.
  apply: RcontraR nonmin_n => kf'n; exists fz => [i _ | i j lt_ij le_j_n1].
    by rewrite /fz; case: ifP => // /k_f.
  rewrite /fz (leq_trans lt_ij) //; have [|_ k_fiz] := ifP; first exact: inj_fk.
  by case: kf'n; exists i => //; apply/ltP/(leq_trans lt_ij).
have [k kPn k_f]: exists2 k, is_prefix k & inmf nc.+1 k f.
  elim: {-2}nc.+1 (ltnSn nc) => [|n IHn] le_nnc.
    by have [k kP] := prefix_coloring_exists 0; exists k; first exists 0.
  have [k1 [n1 inj_k1f] k1_f] := IHn (leqW le_nnc).
  have [k2 [n2 k2Pn] k2_fn] := lim_f n le_nnc.
  have /orP[le_n12 | le_n21] := leq_total n1 n2.
    exists k2 => [|i]; [by exists n2 | rewrite ltnS leq_eqVlt].
    by case/predU1P=> [->|/k1_f]; last apply: (prefix_coloring_le le_n12).
  exists k1 => [|i]; [by exists n1 | rewrite ltnS leq_eqVlt].
  by case/predU1P=> [->|/k1_f]; first apply: (prefix_coloring_le le_n21) k2_fn.
have{lim_f} [nk /prefix_pcoloring[[kP _ [fk fk_k]] _]] := kPn.
pose s_spec n s := forall i (j := nth 0 s i), i < n -> j < nc /\ k (fk j) (f i).
have{fk_k} [s Ls Ds]: exists2 s, size s = nc.+1 & s_spec nc.+1 s.
  elim: nc.+1 => [|n IHn] in f k_f s_spec {inj_limf} *; first by exists [::].
  have [i lt_i_n|s Ls Ds] := IHn (fun i => f i.+1); first exact: k_f.
  have [|j /ltP-lt_j_nc k_fkj_f0] := fk_k (f 0); first exact: k_f.
  by exists (j :: s) => [|[|i] //]; [congr _.+1 | apply: Ds].
have{inj_limf} Us: uniq s.
  rewrite -(mkseq_nth 0 s) map_inj_in_uniq ?iota_uniq // Ls => i1 i2.
  rewrite !mem_iota /= => le_i1n le_i2n Esi12.
  without loss lt_i12: i1 i2 le_i1n le_i2n Esi12 / i1 < i2.
    by move=> IHi; case: (ltngtP i1 i2) => // /IHi->.
  have [[_ k_s_fi1] [_ k_s_fi2]] := (Ds i1 le_i1n, Ds i2 le_i2n).
  have [] := inj_limf i1 i2 lt_i12 le_i2n.
  by exists k => //; apply/(map_transl kP k_s_fi1); rewrite Esi12.
have [s' Ls' Ds']: exists2 s', size s' = nc & s' =i [pred i | i < nc].
  by exists (iota 0 nc) => [|i]; rewrite (size_iota, mem_iota).
case/negP: (ltnn nc); rewrite -Ls -Ls'; apply: uniq_leq_size => // i.
by case/(nthP 0); rewrite Ds' Ls => j /Ds[lt_j_nc _] <-.
Qed.

Lemma compactness_extension : colorable_with nc m0.
Proof.
by move: limit_coloring_coloring size_limit_coloring; exists limit_coloring.
Qed.

End FinitizeMap.
