(* (c) Copyright 2006-2018 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrfun ssrbool eqtype ssrnat seq choice fintype path fingraph.
From fourcolor
Require Import hypermap.

(******************************************************************************)
(* The Walkup construction (as described by Stahl) removes a point from the   *)
(* domain of a hypermap, suppressing it from two of the three permutations.   *)
(* The third permutation then needs a slightly more complex adjustment to     *)
(* reestablish the triangular identity. Because of this asymmetry, there are  *)
(* are actually three ways of applying the transformation. It turns out that  *)
(* all three variants are useful in proving the Jordan/Euler equivalence, and *)
(* later in the four color theorem proof (WalkupE is used in cubic.v, WalkupN *)
(* in kempe.v, and WalkupF in contract.v)!                                    *)
(*   For G : hypermap and z : G, we define                                    *)
(*    skip injf == The function on {y | y != z} obtained from f : G -> G such *)
(*                 that injf : injective f, by "skipping" over z; the cycle   *)
(*                 representation of skip injf is that of f with z removed.   *)
(*      skip1 f == The self-expanding function in G that corresponds to       *)
(*                 skip injf, when injf : injective f.                        *)
(*    skip_edge == An explicit inverse to skip nodeI \o skip faceI.           *)
(*                 (The corresponding self-expanding function is skip_edge1.) *)
(*    WalkupE z == The hypermap whose edge, node and face permutations are    *)
(*                 skip_edge, skip nodeI, skip faceI, respectively.           *)
(*    WalkupN z == The hypermap whose edge and face permutations are          *)
(*                 skip edgeI and skip faceI.                                 *)
(*    WalkupF z == The hypermap whose edge and node permutations are          *)
(*                 skip edgeI and skip nodeI.                                 *)
(* cross_edge z <=> z and node z are on the same edge cycle. This edge cycle  *)
(*                 will be split in two in WalkupE z if z is not degenerate,  *)
(*                 i.e., ~~ glink z z. Conversely, if cross_edge z does not   *)
(*                 hold or if z if degenerate, the genus and hence the Euler  *)
(*                 planarity condition are invariant.                         *)
(*  skip_edge_domain z == the domain of the edge cycles of G that change in   *)
(*                 WalkupE z.                                                 *)
(* Aside from these definitons, the main results proved here are that both    *)
(* the Euler and Jordan planarity conditions are preserved by all Walkup      *)
(* transforms; these will be used to prove the equivalence of these two       *)
(* conditions in file jordan.v.                                               *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Walkup.

Variables (G : hypermap) (z : G).
Implicit Types x y : G.

Let tG' : predArgType := {x | x != z}.

Let inG' x neq_xz : tG' := Sub x neq_xz.

Let z'G' (u : tG') : (val u == z) = false. Proof. exact: negPf (valP u). Qed.

Section Skip.

Variable f : G -> G.
Hypothesis injf : injective f.
Implicit Types u v : tG'.

Definition skip1 := [fun x => [eta id with z |-> f z] (f x)].

Fact skip_subproof u : skip1 (val u) != z.
Proof.
apply: contraNneq (valP u) => /=; case: eqP => // fu_z fz_z.
by rewrite -(inj_eq injf) fu_z fz_z.
Qed.
Definition skip u := inG' (skip_subproof u).

Fact inj_skip : injective skip.
Proof.
case=> [x z'x] [y z'y]; apply: contra_eq; rewrite -!val_eqE /= => y'x.
have [Dfx | _] := f x =P z; last by case: ifP; rewrite (inj_eq injf).
by rewrite -[in f y == z]Dfx ifN (inj_eq injf) eq_sym.
Qed.

Lemma valE_skip u v : val v = f (val u) -> v = skip u.
Proof. by move=> def_v; apply: val_inj; rewrite /= -def_v z'G'. Qed.

Lemma base_skip : fun_base val f skip (pred1 (finv f z)).
Proof. by move=> *; congr (_ == _); rewrite /= (canF_eq (finv_f injf)) ifN. Qed.

Lemma fconnect_skip u v : fconnect skip u v = fconnect f (val u) (val v).
Proof.
apply/idP/idP; rewrite /= fconnect_orbit => /trajectP[n _ Dv].
  rewrite {v}Dv fconnect_sym; elim: n => //= n; rewrite same_fconnect1 //.
  by case: eqP => // ->; rewrite same_fconnect1.
elim: {n}n.+1 {-2}n (ltnSn n) => // m IHm n lemn in u Dv *.
case: n => [|n] in Dv lemn; first exact/eq_connect0/val_inj.
have ltn1m: n - (f (val u) == z) < m by rewrite (leq_ltn_trans (leq_subl _ _)).
rewrite (same_fconnect1 inj_skip) (IHm _ ltn1m) //= -fun_if -subSKn -iterSr.
case: eqP => // Dfu; rewrite -[in RHS]Dfu -iterSr subn1 prednK // lt0n.
by apply: contraFneq (z'G' v) => /= n_0; rewrite Dv iterSr Dfu n_0.
Qed.

Lemma fcard_skip : (f z == z) + fcard skip tG' = fcard f G.
Proof.
have symf := fconnect_sym injf; have symf' := fconnect_sym inj_skip.
pose a := fconnect f z.
have Cfa': fclosed f (predC a) by apply/predC_closed/connect_closed.
have adj_f: fun_adjunction val f skip (predC a).
  apply: (strict_adjunction symf' Cfa' val_inj) => [|u v a'u].
    apply/subsetP=> x a'x; apply: (codom_f _ (inG' _)).
    by apply: contraNneq a'x => ->; apply: connect0.
  by apply/base_skip/(contraNneq _ a'u) => -> /=; rewrite !inE /a fconnect_finv.
rewrite (n_compC a) (n_compC (preim val a)) {3}/a (n_comp_connect symf).
rewrite (adjunction_n_comp _ symf symf' Cfa' adj_f) addnA; congr (_ + _).
have [fz_z | z'fz] := altP (f z =P z).
  have /fconnect_cycle-cyc_z: fcycle f [:: z] by rewrite /= fz_z eqxx.
  by apply/eqP/pred0P=> u /=; rewrite andbC [u \in preim val a]cyc_z inE ?z'G'.
apply: etrans (n_comp_connect symf' (inG' z'fz)).
by apply: eq_n_comp_r => u; rewrite !inE fconnect_skip -same_fconnect1.
Qed.

End Skip.

Local Notation nz := (node z).
Local Notation fz := (face z).
Local Notation ez := (edge z).

Definition skip_edge1 := [fun x =>
  if ez == z then edge x else
  if face (edge x) == z then ez else
  if edge x == z then edge nz else edge x].

Fact skip_edge_subproof (u : tG') : skip_edge1 (val u) != z.
Proof.
case: u ifPn => x z'x /= [/eqP <- | z'ez]; first by rewrite (inj_eq edgeI).
by case: ifPn => //; case: ifPn => // /eqP->; rewrite (canF_eq faceK) eq_sym. 
Qed.

Definition skip_edge u := inG' (skip_edge_subproof u).

Lemma skip_edgeK : cancel3 skip_edge (skip nodeI) (skip faceI).
Proof.
case=> x z'x; apply/val_inj; rewrite /= !(canF_eq edgeK).
have /altP[fex_z | z'fex] := face (edge x) =P z.
  have nz_x: nz = x by rewrite -fex_z edgeK.
  rewrite ifT //; case z_nfz: (z == _); first by rewrite fex_z eqxx eq_sym.
  by rewrite ifN_eqC ?edgeK // -(canF_eq nodeK) nz_x.
case: (z == _); first by rewrite (negPf z'fex) edgeK ifN.
have [x_nfz | _] := x =P node fz; first by rewrite nodeK eqxx -x_nfz ifN.
by rewrite (negPf z'fex) edgeK ifN.
Qed.
Definition WalkupE := Hypermap skip_edgeK.
Local Notation G' := WalkupE.
Implicit Types u v : G'.

Definition WalkupI u x : G' := insubd u x.

Lemma WalkupI_eq u x : val (WalkupI u x) = (if z == x then val u else x).
Proof. by rewrite val_insubd if_neg eq_sym. Qed.

Lemma Walkup_seq (p : seq G) : z \notin p -> {q : seq G' | map val q = p}.
Proof.
move=> p'z; exists (pmap insub p); rewrite (pmap_filter (insubK _)).
by apply/all_filterP/allP=> x p_x; rewrite insubT //= (memPn p'z).
Qed.

Lemma base_skip_edge : @fun_base G G' val edge edge (pred2 (node fz) nz).
Proof.
move=> u v /=; rewrite -val_eqE /= -(canF_eq edgeK) => /norP[/negPf-> nz'u].
by rewrite (canF_eq (canF_sym nodeK)) (negPf nz'u) if_same.
Qed.

Lemma glink_fp_skip_edge : glink z z -> skip_edge =1 skip edgeI.
Proof.
rewrite /glink /= => zGz [x z'z]; apply: val_inj => /=.
case: eqP zGz => [ez_z _ | _ /pred2P[nz_z | fz_z]]; first by case: eqP => // ->.
  by rewrite -(inj_eq nodeI) edgeK nz_z ifN.
by rewrite -[in face (edge x) == z]fz_z (inj_eq faceI); case: (edge x == z).
Qed.

Definition cross_edge := cedge z (node z).

Let z_comp := closure clink (@preim G' G val (clink z)).
Let z_barb := clink z \subset pred1 z.

Let z_barb_z : z_barb = [&& ez == z, nz == z & fz == z].
Proof.
apply/subsetP/idP => [zGz | /and3P[_ /eqP-nz_z /eqP-fz_z] x]; last first.
  by rewrite unfold_in /= -nz_z (finv_f nodeI) nz_z fz_z eq_sym orbb.
have /eqP-fz_z := zGz _ (clinkF z); rewrite (canF_eq edgeK) fz_z eqxx andbT.
by rewrite eq_sym andbb (canF_eq (finv_f nodeI)) eq_sym; apply/zGz/pred2P; left.
Qed.

Let clink_at_G' u v : clink (val u) (val v) -> clink u v.
Proof.
rewrite !(sameP clinkP pred2P) -!val_eqE /=.
by case/pred2P=> [<- | ->]; rewrite z'G' eqxx ?orbT.
Qed.

Let clink_at_G u v : connect clink u v -> connect clink (val u) (val v).
Proof.
case/connectP=> {v} p uCp ->.
elim: p u uCp => //= v p IHp u /andP[uCv /IHp{IHp}]; apply: connect_trans.
case/clinkP: uCv => [-> | <-] /=.
  by case: eqP => [{1}<-|]; rewrite !(same_connect1 clinkC (clinkN _)).
by case: eqP => [{2}<-|]; rewrite -!(same_connect1r clinkC (clinkF _)).
Qed.

Let z_comp_preimage : z_comp =1 preim val (connect clink z).
Proof.
move=> v; apply/pred0Pn/idP=> [[u /andP[/= vCu zCu]]| /connectP[p0]].
  by rewrite (same_connect_r clinkC (clink_at_G vCu)) connect1.
case/shortenP=> -[_ _|x p /= zCp /andP[p'z _]] _; first by have /eqP := z'G' v.
have{p0 zCp p'z} [[zCx xCp] [[|u q] //= [Du Dq]]] := (andP zCp, Walkup_seq p'z).
rewrite -Du -Dq last_map in zCx xCp * => /val_inj-Lq.
exists u; rewrite !inE {}zCx andbT (@clinkC G').
apply/connectP; exists q => //; apply/(pathP u)=> i ltiq; apply: clink_at_G'.
by rewrite -!(nth_map u x) // 1?ltnW // (pathP x xCp) ?size_map.
Qed.

Let z_barb_comp : z_barb = (n_comp clink z_comp == 0).
Proof.
apply/subsetP/pred0P => [sGzz u | sGzz x zCx].
  by apply/andP=> -[_ /existsP[v /andP[_ /sGzz]]]; rewrite inE z'G'.
apply/wlog_neg=> z'x; pose u : G' := inG' z'x.
have /idP[]:= sGzz (root clink u); rewrite /= (roots_root (@clinkC G')).
by apply/existsP; exists u; rewrite !inE (@clinkC G') connect_root.
Qed.

Let disconnected := 1 < n_comp clink z_comp.

Let n_comp_z disc := if glink z z then z_barb.+1 else ~~ disc : nat.

Let not_cross_edge_Walkup u v :
  ~~ cross_edge -> val u = ez -> val v = node fz -> cedge u v.
Proof.
move=> not_zEnz Du Dv; have /eqP-ez'z: z != ez by rewrite eq_sym -Du z'G'.
have /connectP[p0 ezEp Lp]: cedge ez z by rewrite cedgeC ?fconnect1.
do [case/shortenP: ezEp => /lastP[//|p t] ezEp Up _; rewrite last_rcons] in Lp.
rewrite -{t}Lp rcons_path -rcons_cons !(inE, lastI, rcons_uniq) in ezEp Up.
have{ezEp Up} [[ezEp /eqP-Lp] [/norP[_ p'z] p'nfz _]] := (andP ezEp, and3P Up).
have [q Dq] := Walkup_seq p'z; apply/connectP.
exists q; last by apply/val_inj/edgeI; rewrite -last_map Du Dq Dv faceK.
rewrite -(map_path base_skip_edge) -?has_map -?belast_map Dq Du //.
rewrite has_predU !has_pred1 -(canRL edgeK Lp) negb_or {}p'nfz.
by apply: contra not_zEnz => /mem_belast/(path_connect ezEp); rewrite -cedge1.
Qed.

Let disconnected_cross_edge : disconnected -> ~~ glink z z /\ cross_edge.
Proof.
move=> not_cc_z; apply/andP; apply: contraLR not_cc_z => zGz.
rewrite -leqNgt leq_eqVlt orbC -implyNb ltnS leqn0 -z_barb_comp.
apply/implyP=> /subsetPn[x zCx z'x]; pose u : G' := inG' z'x.
have{zCx} zCu: clink z (val u) by [].
rewrite -(n_comp_connect clinkC u); apply/eqP/eq_n_comp_r=> v.
rewrite inE clinkC; apply/'exists_andP/idP=> [[w [vCw zCw]]|]; last by exists u.
apply: connect_trans {v}vCw _; rewrite clink_glink glinkC.
without loss Dw: u w zCu {zCw} / fz = val w.
  move=> IHw; have [Dnw | /IHw-> //] := clinkP zCw.
  have [Dnu | ] := clinkP zCu; last by rewrite glinkC => /IHw->.
  by apply/eq_connect0/val_inj/nodeI; rewrite -Dnw.
have [/(canLR nodeK)Du | ] := clinkP zCu; last by rewrite Dw => /val_inj->.
have [ez_z| z'ez] := eqVneq (edge z) z; last pose v : G' := inG' z'ez.
  by apply/eq_connect0/val_inj; rewrite -Du ez_z.
have <-: face v = u by apply/val_inj; rewrite /= Du z'G'.
rewrite -(same_connect1 glinkC (glinkF v)) (same_connect1r glinkC (glinkN w)).
suffices: cedge v (node w).
  by apply/connect_sub=> u1 _ /(@eqP G')<-; rewrite connect1 ?glinkE.
rewrite !negb_or /= z'ez (canF_eq nodeK) Du Dw eq_sym !z'G' /= in zGz.
by rewrite not_cross_edge_Walkup //= -Dw ifN_eqC // -(canF_eq edgeK).
Qed.

Let not_cross_connected : ~~ cross_edge -> ~~ disconnected.
Proof. by apply: contra => /disconnected_cross_edge[]. Qed.

Definition skip_edge_domain := [pred x | has (cedge x) [:: z; node z]].
Local Notation edom := skip_edge_domain.

Let eCedom : fclosed edge (predC edom).
Proof. by move=> x _ /eqP<-; rewrite !inE /= -!cedge1. Qed.
 
Let adj_edom : @fun_adjunction G G' val edge edge (predC edom).
Proof.
apply: (strict_adjunction (@cedgeC G') eCedom val_inj) => [|u v edom'x].
  apply/subsetP=> x edom'x; apply: codom_f (inG' _).
  by rewrite (memPnC edom'x) ?inE //= connect0.
apply/base_skip_edge; apply: contra edom'x; rewrite !inE /= cedge1.
by case/pred2P=> ->; rewrite ?faceK connect0 ?orbT.
Qed.

Lemma same_cskip_edge {u v} :
  ~~ edom (val u) -> cedge u v = cedge (val u) (val v).
Proof. by move=> edom'u; have [_ ->] := adj_edom. Qed.

Lemma sub_cskip_edge u v : ~~ cross_edge -> cedge (val u) (val v) -> cedge u v.
Proof.
have [zGz | /norP[z'ez _]] := boolP (glink z z).
  by rewrite (eq_fconnect (glink_fp_skip_edge zGz)) fconnect_skip.
move=> not_zEnz /connectP[p]; move: {2}_.+1 (ltnSn (size p)) => n lt_p_n.
elim: n p => [|n IHn] [|y p] // in u lt_p_n *; first by move=> _ /val_inj->.
have [-> | z'y] := eqVneq y z => /=/andP[/eqP-Deu].
  case: p => [|ez p] /=/ltnW in lt_p_n *; first by have /eqP := z'G' v.
  case/andP=> /eqP{ez}<- _ /(IHn p (inG' z'ez))/(connect_trans _)-> //.
  by rewrite cedgeC not_cross_edge_Walkup // -(canRL edgeK Deu).
pose w : G' := inG' z'y => _ /(IHn p w)/(connect_trans _)-> {p lt_p_n}//.
have [Dfy | z'fy] := eqVneq (face y) z; last first.
  by rewrite connect1 //= -val_eqE /= Deu !ifN.
suffices: cedge (edge u) (node (face w)) by rewrite -cedge1 cedge1r faceK.
have z'nfz: node fz != z by rewrite eq_sym -(canF_eq edgeK).
by rewrite not_cross_edge_Walkup //= ?Deu Dfy eqxx !ifN.
Qed.

Lemma cskip_edge_merge {u v} :
  ~~ cross_edge -> edom (val u) -> cedge u v = edom (val v).
Proof.
move=> not_zEnz edom_u; apply/idP/idP => [uEv | edom_v].
  apply: contraLR edom_u => edom'v; apply: etrans (edom'v).
  by apply: (closed_connect eCedom); rewrite cedgeC -same_cskip_edge // cedgeC.
without loss uEz: u v {edom_u} edom_v / cedge (val u) z.
  move=> IHu; have [/IHu->|uEnz|] // := or3P edom_u.
  rewrite cedgeC; have [/IHu->|vEnz|] // := or3P edom_v.
  by rewrite sub_cskip_edge // (connect_trans vEnz) // cedgeC.
have{edom_v} [vEz|vEnz|] // := or3P edom_v.
  by rewrite sub_cskip_edge // (connect_trans uEz) // cedgeC.
have z'ez: ez != z.
  apply: contraL uEz => ez_z; have zEz: fcycle edge [:: z] by rewrite /= ez_z.
  by rewrite cedgeC (fconnect_cycle zEz) inE ?z'G'.
have z'nfz: node (face z) != z by rewrite eq_sym -(canF_eq edgeK).
have uEnz: cedge u (inG' z'nfz) by rewrite sub_cskip_edge //= cedge1r faceK.
rewrite (connect_trans uEnz) // cedge1 cedgeC sub_cskip_edge //=.
rewrite faceK eqxx !ifN -?cedge1r // (contraNneq _ not_zEnz) // => fz_z.
by rewrite [cross_edge]cedge1r -(canRL faceK fz_z).
Qed.

Let fcard_skip_edge :
  let Sez := if glink z z then (ez == z).+1 else (~~ cross_edge).*2 in
  Sez + fcard edge G' = (fcard edge G).+1.
Proof.
have [eCG eCG'] := (@cedgeC G, @cedgeC G').
have [zGz | /norP/=[z'ez /norP/=[z'nz z'fz]]] := boolP (glink z z).
  by rewrite /= -(fcard_skip edgeI) (eq_fcard (glink_fp_skip_edge zGz)).
have z'nfz: node fz != z by rewrite eq_sym -(canF_eq edgeK).
pose w : G' := inG' z'nfz; pose w1 : G' := inG' z'nz.
rewrite (n_compC (preim val edom)) (n_compC edom) addnA -addSn.
congr (_ + _); last exact/esym/adjunction_n_comp.
have /eq_n_comp_r->: edom =i fclosure edge (pred2 z nz).
  move=> x; apply/hasP/'exists_andP=> /= -[y]; first by rewrite !inE; exists y.
  by case; exists y; rewrite ?inE.
have /eq_n_comp_r->: preim val edom =1 fclosure edge (pred2 w w1).
  apply/fsym=> u; apply/'exists_andP/idP=> /= [[v [vEu Dv]] | edom_u].
    apply/idPn=> edom'u; rewrite inE (same_cskip_edge edom'u) in vEu.
    rewrite [~~ _](closed_connect eCedom vEu) !inE /= in edom'u.
    by case/pred2P: Dv edom'u => ->; rewrite cedge1 ?faceK connect0 ?orbT.
  pose edom1 := pred2 (val w) (val w1).
  have{edom_u}[_ /connectP[p uEp ->]]: exists2 y, cedge (val u) y & y \in edom1.
    have [uEz | uEnz | //] := or3P edom_u.
      by exists (val w); rewrite ?inE ?eqxx // cedge1r faceK.
    by exists (val w1); rewrite //= !inE eqxx orbT.
  elim: p => [|y p IHp] /= in u uEp *; first by exists u; rewrite ?inE.
  have{uEp} [/eqP-Deu euEp] := andP uEp => Lp.
  have [Dy | /norP[z'y z'fy]] := boolP [|| y == z | face y == z].
    exists u; rewrite !inE -!val_eqE.
    by rewrite -(canF_eq edgeK) -(canF_eq (canF_sym nodeK)) Deu.
  have{IHp euEp Lp} [v [yEv Dv]] := IHp (inG' z'y) euEp Lp; exists v.
  by rewrite inE (connect_trans _ yEv) ?connect1 //= -val_eqE /= Deu !ifN.
rewrite !n_comp_closure2 // -/cross_edge.
have [zEnz | not_zEnz] := boolP cross_edge; last first.
  by rewrite cskip_edge_merge //= cedge1 ?faceK connect0 ?orbT.
have{zEnz} /connectP[p0]: cedge (val w) (val w1) by rewrite cedge1 faceK.
case/shortenP=> [[_ | _ p /=/andP[/eqP<- zEp]] Up _ {p0}] /= Lp.
  by rewrite -(nodeI Lp) eqxx in z'fz.
rewrite faceK inE (negPf z'nfz) /= in zEp Up Lp.
have{Up} [p'nfz /Walkup_seq[q Dq] Up] := and3P Up.
suffices cycEq: fcycle edge q.
  rewrite eCG' (fconnect_cycle cycEq) -(mem_map val_inj) Dq ?p'nfz //=.
  by have /eqP := z'nz; rewrite Lp; case: {+}p => //= ez p1; rewrite mem_last.
case: q => //= ew q in Dq *; rewrite rcons_path /= andbC -val_eqE /= ifN //.
rewrite -Dq {1 2}lastI /= rcons_uniq mem_rcons inE last_map in p'nfz Up Lp zEp.
have{Up p'nfz} [[_ q'nfz] [q'nz _]] := (norP p'nfz, andP Up).
rewrite -Lp nodeK !eqxx -(map_path base_skip_edge) {zEp}//.
by rewrite -has_map -belast_map has_predU !has_pred1 Lp negb_or q'nfz.
Qed.

Lemma base_clink_Walkup : @rel_base G G' val clink clink (pred2 (edge nz) nz).
Proof.
move=> u v /norP[]; rewrite -(canF_eq faceK) => z'fu nz'u.
rewrite !(sameP clinkP pred2P) -!val_eqE /= (negbTE z'fu); congr (_ || _).
by case: (_ =P z) => // ->; rewrite z'G' (negbTE nz'u).
Qed.

Lemma card_Walkup : #|G'| = #|G|.-1.
Proof. by rewrite card_sub cardC1. Qed.

Lemma card_S_Walkup : #|G| = #|G'|.+1.
Proof. by rewrite card_Walkup (cardD1 z). Qed.

Let n_comp_glink_Walkup :
  n_comp_z disconnected + n_comp glink G' = (n_comp glink G).+1.
Proof.
have [eCG eCG'] := (@clinkC G, @clinkC G'); pose a := connect clink z.
have cCa: closed clink (predC a) by apply/predC_closed/connect_closed.
have adj_a: @rel_adjunction G G' val clink clink (predC a).
  apply: (strict_adjunction eCG' cCa val_inj) => [|u v /negPn/=a'v].
    apply/subsetP=> x a'x; apply: codom_f (inG' _).
    by apply: contraNneq a'x => ->; apply: connect0.
  apply: base_clink_Walkup; apply: contra a'v => /pred2P[] ->.
    by rewrite [a _]eCG connect1 // -{2}[z]nodeK clinkF.
  by rewrite [a _]eCG connect1 // clinkN.
rewrite -2!(eq_n_comp (@clink_glink _)) (n_compC (preim val a)) (n_compC a).
rewrite addnA -addSn; congr (_ + _); last exact/esym/adjunction_n_comp.
rewrite /a (n_comp_connect eCG) -(eq_n_comp_r z_comp_preimage) /n_comp_z.
have [not_cc_z | ] := boolP disconnected; last first.
  rewrite -leqNgt leq_eqVlt ltnS leqn0 z_barb_comp.
  case/pred2P=> nc_z; rewrite nc_z ?if_same ?ifT // [glink z z]subrelUl //=.
  by have:= esym z_barb_z; rewrite z_barb_comp nc_z => /and3P[].
have [not_zGz _] := disconnected_cross_edge not_cc_z.
apply/eqP; rewrite (negPf not_zGz) eqn_leq -/disconnected not_cc_z andbT add0n.
have{not_zGz} /norP[_ /norP/=[z'nz z'fz]] := not_zGz.
have{z'nz} z'fez: face ez != z by rewrite eq_sym -(canF_eq nodeK).
pose u : G' := inG' z'fez; pose v : G' := inG' z'fz.
suffices /eq_n_comp_r->: z_comp =1 closure clink (pred2 u v).
  by rewrite n_comp_closure2 // ltnS leq_b1.
move=> w; congr (~~ _); apply: {w}eq_disjoint_r => w; rewrite !inE !(eq_sym w).
by rewrite (sameP clinkP pred2P) -!val_eqE (canF_eq (canF_sym nodeK)).
Qed.

Let Euler_lhs_WalkupE :
  (n_comp_z disconnected).*2 + Euler_lhs G' = (Euler_lhs G).+1.
Proof.
by rewrite /Euler_lhs card_S_Walkup addnA -doubleD n_comp_glink_Walkup addnS.
Qed.

Let Euler_rhs_WalkupE :
  (n_comp_z cross_edge).*2 + Euler_rhs G' = (Euler_rhs G).+1.
Proof.
rewrite -addSn -fcard_skip_edge -(fcard_skip faceI) -(fcard_skip nodeI).
rewrite [t in _ + _ + t]addnACA addnACA /n_comp_z z_barb_z; congr (_ + _).
rewrite /glink /=; case ez_z: (ez == z).
  by rewrite (canF_eq nodeK) (eqP ez_z) eq_sym andbb addnn.
  have [nz_z | _] /= := nz =P z; last by rewrite addnC; case: ifP.
by rewrite (canF_eq faceK) eq_sym nz_z ez_z.
Qed.

Lemma genus_WalkupE_eq : glink z z \/ ~~ cross_edge -> genus G' = genus G.
Proof.
rewrite /(genus G) -subSS -Euler_lhs_WalkupE -Euler_rhs_WalkupE /n_comp_z.
by case=> [-> | not_zEnz]; rewrite ?(not_zEnz, not_cross_connected) ?subnDl.
Qed.

Lemma le_genus_WalkupE : genus G' <= genus G.
Proof.
have [/orP/genus_WalkupE_eq-> // |] := boolP (glink z z || ~~ cross_edge).
case/norP=> zG'z /negPn-zEnz; rewrite /(genus G) -subSS.
rewrite -Euler_lhs_WalkupE -Euler_rhs_WalkupE /n_comp_z !ifN // zEnz.
by rewrite half_leq // leq_sub2r ?leq_addl.
Qed.

Lemma planar_WalkupE : planar G -> planar G'.
Proof. by rewrite /planar -!leqn0 => /(leq_trans le_genus_WalkupE). Qed.

Lemma even_genus_WalkupE : even_genus G' -> even_genus G.
Proof.
move=> evenG'; apply/eqP; rewrite -eqSS /genus -subSS -Euler_lhs_WalkupE evenG'.
rewrite -addnS -Euler_rhs_WalkupE addnCA 2!addnA subnDr eqn_add2r.
rewrite -doubleD -doubleB half_double -doubleD subnK // addnC /n_comp_z.
by case: glink cross_edge not_cross_connected => [|[|->]]; rewrite ?leq_addr.
Qed.

(******************************************************************************)
(*   We prove here that the WalkupE step preserves the Jordan property,       *)
(* i.e., that any Moebius path in G' can be lifted to a Moebius path in G.    *)
(*   This is because N-links and F-links (and hence C-links) are mostly       *)
(* preserved by the G' -> G injection: the only possible discrepancy is that  *)
(* F- and N-links in G' may skip over z. This can be fixed by inserting z in  *)
(* while lifting Moebius C-path from G to G'. However, we may need to do this *)
(* twice, in which case part of the C-path needs to be deleted in order to    *)
(* recover a duplicate-free path. This part to be deleted part depends on the *)
(* position z is inserted, relative to the endpoints of the two explicit      *)
(* crossing N-links prescribed by the Moebius predicate. This gives rise to   *)
(* 13 cases in the proof below.                                               *)
(*  In more detail, we consider two other kinds of C-links in G, besides the  *)
(* the standard (clink) ones: those projected from G', which may skip over z  *)
(* (relation clink2 below), and an intermediate kind (clink1) which can only  *)
(* skip over z if it is a projected F-link.                                   *)
(*   We first consider the cases where the projected C-path is a clink or     *)
(* clink1 path; there we may need to insert z in the crossing N-links or the  *)
(* main contour, but not both. In the other cases, the C-path splits into two *)
(* cink1 paths, the crossing N-links are N-links in G, and the part of the    *)
(* path we have to delete if there is also an F-link skipping over z is       *)
(* determined by which crossing link endpoint lies between the skipping N-    *)
(* and F-links.                                                               *)
(*   It is possible to give a more compact proof sketch by making use of an   *)
(* alternative presentation of Moebieus path as three parallel, internally    *)
(* disjoint C-paths between two end darts, two forward and one reverse, where *)
(* the forward paths start and end with different C-link types. Up to all the *)
(* symmetries there are only 3 cases: either z is inserted at most once,      *)
(* or twice in the same branch (then one deletes the path between the two     *)
(* instancese), or in two different branches. In the last case z must be      *)
(* inserted in at least one branch with different end link types, so that     *)
(* branch contains a path between z and one of the end darts (say t), with    *)
(* different end link types, so deleting the rest of the branch yields a      *)
(* Moebius path with end darts z and t. Unfortunately it turns out that the   *)
(* formalization of this more synthetic proof is longer, due to the extra     *)
(* work juggling the more complex characterization and exposing symmetries.   *)
(******************************************************************************)

Lemma Jordan_WalkupE : Jordan G -> Jordan G'.
Proof.
pose t := finv node z; have GnK := finv_f (@nodeI G).
have [nt_z zCt]: node t = z /\ clink z t by rewrite -(f_finv nodeI z) clinkN.
pose clink1 x y := (x == node y) || (skip1 face x == y).
pose clink2 x y := (x == skip1 node y) || (skip1 face x == y).
have cpath1I x p: path clink2 x p -> t \notin p -> path clink1 x p.
  move=> xCp p't; apply/(pathP z)=> i ltip; rewrite /clink1 orbC.
  have:= pathP z xCp i ltip; rewrite /clink2 orbC; case: (_ == _) => //=.
  by rewrite (canF_eq GnK) ifN // (memPn p't) ?mem_nth.
have cpathI x p: path clink1 x p -> fz \notin p -> path clink x p.
  move=> xCp p'fz; apply/(pathP z)=> i ltip; apply/clinkP/pred2P.
  have:= pathP z xCp i ltip; rewrite /clink1 /=; case: (_ == node _) => //=.
  by case: ifP => // _ /idPn[]; rewrite (memPnC p'fz) ?mem_nth.
have cpath1P x p: path clink1 x p -> ~~ path clink x p -> uniq p ->
  exists p1, exists p2, [/\ fz \in p, p = p1 ++ p2, last z p2 = last x p,
                            path clink x (rcons p1 z) & path clink z p2].
- move=> xCp not_xCp Up; have p_fz: fz \in p by apply: contraR (cpathI x p _) _.
  rewrite p_fz; case/splitPr: p_fz Up xCp not_xCp => p1 p2; rewrite !cat_path.
  rewrite /= cat_uniq => /and4P[_ /norP[p1'fz _] p2'fz _] /and3P[p1P p1Cfz p2P].
  have [xCp1 fzCp2]: path clink x p1 /\ path clink fz p2 by rewrite !cpathI.
  rewrite xCp1 fzCp2 andbT /= => /clinkP/pred2P-not_p1Cfz.
  exists p1, (fz :: p2); rewrite last_cat /= clinkF rcons_path xCp1; split=> //.
  by apply: contraLR p1Cfz => /norP[_ /= z'fp1]; rewrite /clink1 /= ifN.
move=> JordanG [|u q] //; apply/and3P=> -[Uq uCq qvnu].
pose x := val u; pose y := val (finv node (last u q)); pose p := map val q.
have Lp: last x p = skip1 node y by rewrite last_map -(f_finv nodeI (last u q)).
have{qvnu} pynx: mem2 p y (skip1 node x) by rewrite -(mem2_map val_inj) in qvnu.
rewrite /= !(canF_eq GnK) -/t in Lp pynx.
have{Uq} Uzp: uniq ([:: z] ++ x :: p).
  rewrite -map_cons cons_uniq (map_inj_uniq val_inj).
  by rewrite -has_pred1 has_map (eq_has z'G') has_pred0.
have{uCq} xCp: path clink2 x p; last move {u q} in (p) (x) (y) Uzp xCp pynx Lp.
  apply: etrans uCq; apply: map_path pred0 _ _ _ _; last by rewrite has_pred0.
  by move=> v w; rewrite (sameP clinkP pred2P).
have [p'x Up]: x \notin p /\ uniq p by case/and3P: Uzp.
have y'x: x != y by rewrite (memPnC p'x) // (mem2l pynx).
have not_xCp: ~~ path clink x p.
  apply: contra (JordanG (x :: p)) => {xCp}xCp; rewrite /= p'x Up xCp /=.
  case: eqP => [y_t | _] in Lp; rewrite Lp GnK; last first.
    case: eqP => // x_t in pynx; have/and3P[] := JordanG [:: z, x & p].
    by rewrite Uzp /= Lp GnK -cat1s mem2_cat pynx orbT xCp x_t zCt.
  have/and3P[] := JordanG (x :: rcons p z); rewrite last_rcons -/t -y_t.
  rewrite rcons_path xCp Lp clinkN -cats1 -cat_cons uniq_catC Uzp.
  by rewrite -y_t ifN // in pynx; rewrite mem2_cat pynx.
have{not_xCp y'x} not_xCp: ~~ path clink1 x p.
  apply/negP=> /cpath1P[] {not_xCp}// p1 [p2 [_ Dp Lp2 xCp1 zCp2]]. 
  rewrite Dp -cat_cons uniq_catCA in Uzp.
  have /and3P[] := JordanG (x :: p1 ++ z :: p2); rewrite Uzp last_cat /= Lp2.
  split=> //; first by rewrite -cat_rcons cat_path xCp1 last_rcons.
  case: eqP => [y_t | _] in Lp; rewrite Lp GnK; last first.
    do [rewrite Dp; case: eqP => [x_t|_]] in pynx; last by rewrite mem2_splice1.
    rewrite mem2_cat x_t nt_z mem_head andbT; apply/orP; right.
    apply: contraR (JordanG (z :: p2)) => p1'y; rewrite mem2l_cat // in pynx.
    by apply/and3P; rewrite (subseq_uniq _ Uzp) ?suffix_subseq // Lp2 Lp GnK.
  rewrite mem2_cat mem2_cons eqxx /= mem_behead ?orbT //=.
  apply: contraR (JordanG (x :: rcons p1 z)) => p2'nx; apply/and3P.
  rewrite xCp1 last_rcons -cats1 (subseq_uniq _ Uzp) ?catA ?prefix_subseq //.
  by rewrite -y_t ifN // Dp mem2r_cat // y_t in pynx; rewrite mem2_cat pynx.
have p_t: t \in p by apply: contraR (cpath1I x p _) _.
have{pynx p'x} pynx: mem2 p y (node x) by rewrite ifN ?(memPnC p'x) in pynx.
do [have{p p_t} [p1 p2] := splitPr p_t] in Uzp Up Lp xCp not_xCp pynx.
rewrite !cat_path cat_uniq /= has_sym -cons_uniq in Up xCp not_xCp.
have [[xCp1 p1Ct tCp2] [Up1 /norP[p1't Up21] Utp2]] := (and3P xCp, and3P Up).
have{xCp Up} [p2't Up2]: t \notin p2 /\ uniq p2 by case/andP: Utp2.
have{xCp1 p1't} xCp1: path clink1 x p1 by rewrite cpath1I.
have{tCp2 p2't cpath1I} tCp2: path clink1 t p2 by rewrite cpath1I.
have{not_xCp p1Ct} Lp1: last x p1 = node z.
  case/predU1P: p1Ct => [-> /= | p1Ft]; first by rewrite nt_z eqxx.
  by rewrite xCp1 tCp2 /clink1 p1Ft orbT in not_xCp.
have{Lp} [Lp2 t'y]: last t p2 = node y /\ y != t.
  case: ifPn Lp Uzp; rewrite (lastI x) last_cat => //= _ -> /nandP[]; right.
  by rewrite belast_cat Lp1 rcons_uniq mem_cat mem_head orbT.
have{xCp1 Up21} xCp1: path clink x p1.
  apply/idPn=> /cpath1P[] {xCp1}// q1 [q2 [p1fz Dp1 Lq2 xCq1 zCq2]].
  rewrite {}Dp1 cat_uniq -catA -cat_cons uniq_catCA catA cats1 in Up1 Uzp pynx.
  have{tCp2 p1fz} tCp2: path clink t p2 by rewrite cpathI ?(hasPn Up21).
  have q2'nx: node x \notin q2.
    apply: contra (JordanG (x :: rcons q1 z ++ q2)) => q2nx; apply/and3P.
    rewrite (subseq_uniq _ Uzp) ?catA ?prefix_subseq // last_cat cat_path xCq1.
    by rewrite last_rcons Lq2 Lp1 GnK mem2_cat mem_rcons mem_head q2nx orbT.
  have q2y: y \in q2.
    apply: contraR (JordanG ((x :: rcons q1 z) ++ t :: p2)) => q2'y.
    apply/and3P; rewrite (subseq_uniq _ Uzp) ?cat_subseq ?suffix_subseq //.
    rewrite -/cat last_cat cat_path xCq1 last_rcons /= zCt Lp2 GnK.
    by rewrite cat_rcons mem2_splice1 //; rewrite mem2lr_splice in pynx.
  have{q2'nx pynx Up1} p2nx: node x \in t :: p2.
    rewrite mem2l_cat in pynx; last by case/and3P: Up1 => _ /hasPn->.
    by apply/implyP: q2'nx; rewrite implyNb -mem_cat (mem2r pynx).
  case/splitPr: q2 / q2y Uzp Lq2 zCq2 => q21 q22 Uzp.
  rewrite last_cat cat_path Lp1 /= => Lq22 /and3P[_ _ yCq22].
  have/and3P[] := JordanG (x :: rcons q1 z ++ (t :: p2) ++ y :: q22).
  rewrite -cat_cons uniq_catCA uniq_catC -catA !cat_path !last_cat last_rcons.
  rewrite (subseq_uniq _ Uzp) ?cat_subseq ?suffix_subseq // mem2_cat mem_cat /=.
  by rewrite Lp2 Lq22 GnK mem_rcons mem_head p2nx orbT clinkN xCq1 zCt tCp2.
have /cpath1P[]: ~~ path clink t p2 => {Up2 tCp2}// [|q1 [q2 [_ Dp2]]].
  apply: contra (JordanG (x :: p1 ++ [:: z] ++ t :: p2)) => tCp2.
  apply/and3P; rewrite -cat_cons uniq_catCA Uzp last_cat cat_path /= Lp1 Lp2.
  by rewrite xCp1 clinkN zCt GnK mem2_splice1.
rewrite {}Lp2 {p2}Dp2 -!cat_cons cat_uniq in Utp2 Uzp pynx * => Lq2 tCq1 zCq2.
have{Utp2} Uq21: ~~ has (mem q2) (t :: q1) by rewrite has_sym; case/and3P: Utp2.
rewrite [_ ++ _ ++ q2]catA uniq_catCA -catA in Uzp.
have q1'y: y \notin t :: q1.
  apply: contra (JordanG (t :: rcons q1 z ++ q2)) => q1y; apply/and3P.
  rewrite cat_path tCq1 last_cat last_rcons cat_rcons Lq2 GnK nt_z.
  rewrite (subseq_uniq _ Uzp) ?suffix_subseq //.
  by have:= q1y; rewrite mem2_cat mem_head orbC inE (negPf t'y) => /= ->.
have q1nx: node x \in t :: q1.
  apply: contraR (JordanG (x :: p1 ++ z :: q2)) => q1'nx; apply/and3P.
  rewrite mem2lr_splice // in pynx.
  rewrite -cat_cons (subseq_uniq _ Uzp) ?cat_subseq ?suffix_subseq //.
  by rewrite cat_path last_cat /= Lp1 Lq2 GnK xCp1 clinkN mem2_splice1.
have{q1'y pynx Uq21} p1y: y \in p1.
  rewrite catA mem2r_cat ?(hasPn Uq21) // in pynx.
  by apply/implyP: q1'y; rewrite implyNb orbC -mem_cat (mem2l pynx).
case/splitPl: q1 / q1nx => q11 q12 Lq11 in tCq1 Uzp.
have/and3P[] := JordanG (t :: q11 ++ (x :: p1) ++ z :: q2).
rewrite -cat_cons uniq_catCA (subseq_uniq _ Uzp) ?cat_subseq ?prefix_subseq //.
rewrite !cat_path Lq11 catA last_cat /= Lq2 GnK nt_z Lp1 !clinkN xCp1.
have ->: path clink t q11 by move: tCq1; rewrite rcons_cat cat_path => /andP[].
by rewrite mem2_cat mem_head mem_cat inE p1y !orbT.
Qed.

End Walkup.

Section DualWalkup.

Variables (G : hypermap) (z : G).

Definition WalkupN : hypermap := permF (WalkupE (z : permN G)).
Definition WalkupF : hypermap := permN (WalkupE (z : permF G)).

Lemma planar_WalkupN : planar G -> planar WalkupN.
Proof.
by rewrite /planar genus_permF -(genus_permN G) => /planar_WalkupE->.
Qed.

Lemma planar_WalkupF : planar G -> planar WalkupF.
Proof.
by rewrite /planar genus_permN -(genus_permF G) => /planar_WalkupE->.
Qed.

End DualWalkup.
