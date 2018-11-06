(* (c) Copyright 2006-2018 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrfun ssrbool eqtype ssrnat seq choice fintype path fingraph.
From fourcolor
Require Import hypermap geometry coloring.

(******************************************************************************)
(*   A quiz is a pair of binary trees - questions - that covers the inner     *)
(* regions of a  configuration and stores their arities. The embedding lemmas *)
(* allow us to use questions to actually test for an isomorphic embedding of  *)
(* the configuration in a minimal uncolorable cubic map.                      *)
(* We define:                                                                 *)
(*   qarity == emplicit enumeration of the possible face arities in a         *)
(*             configuration (QaN, with 5 <= N <= 11); qarity coerces to nat. *)
(* qarity_of_nat n == qarity with value n : nat, defaulting to Qa11.          *)
(* question == type of embedding test trees, with leaves Qask0 (no check) and *)
(*             Qask1 qa (check arity qa), unary nodes QaskD qa q, which check *)
(*             arity qa then do a qstepD move in the hypermap before checking *)
(*             recursively q : question, with D in {L, R}, unary QaskDD qa q  *)
(*             node that do a qstepD move BEFORE doing a QaskD qa q check,    *)
(*             and binary nodes QaskLR qa ql qr which recurse twice, after    *)
(*             qstepL and qstepR moves, respectively.                         *)
(* qstepL x == left move at a cubic hypermap node (= node (edge (node x))).   *)
(* qstepR x == right move at a cubic hypermap node (= edge (node x)).         *)
(* isQaskR q <=> q is a QaskR node.                                           *)
(*  flatq q == seq of the qarities occurring in q, collected in prefix order. *)
(*  flipq q == mirror image of q, with L and R exchanged.                     *)
(* walkq q x == sequence of darts visited while testing q at x, in prefix     *)
(*              order. The first dart of the sequence is usually x, except    *)
(*              the sequence for Qask0 is empty, the one for QaskRR starts    *)
(*              with qstepR x, and the one for QaskLL with face^-1 (qstepL x) *)
(*              (the additional face shift ensures the edge-closure of the    *)
(*              traversal stays within the configuration kernel, while not    *)
(*              affecting the outcome of arity tests).                        *)
(* fitq q x == q fits at x: the arities in walkq q x match those in flatq q.  *)
(*     quiz == type of embedding tests, consisting in a pair of 'question's   *)
(*             that test for a preembedding starting from the initial edge of *)
(*             the configuration construction program (see library cfmap).    *)
(* isQuizR qz <=> qz consists of two QaskR questions.                         *)
(*  flatqz qz == seq of the qarities occurring in qz's questions.             *)
(*  flipqz qz == mirror image of qz, with L and R exchanged.                  *)
(* walkqz qz x == sequence of darts visited while testing qz.                 *)
(*  fitqz qz x == qz fits at x: the arities in walkqz qz x match flatqz qz.   *)
(* valid_quiz rc x0c qz <-> qz tests for the configuration with perimeter rc, *)
(*             at initial dart x0c: qz satisfies isQuizR, fits at x0c, and    *)
(*             walkqz qz x0c is a transversal of the faces in kernel rc.      *)
(* embedqz x0m x0c qz == a preembedding of kernel rc into a map Gm that maps  *)
(*             x0c to x0m, assuming qz test for kernel rc at x0c and fits Gm  *)
(*             at x0m (Lemma quiz_preembedding).                              *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* We are only interested in arities between 5 and 11 (in fact 9, 10, and 11 *)
(* only occur at the hub).                                                   *)

CoInductive qarity := Qa5 | Qa6 | Qa7 | Qa8 | Qa9 | Qa10 | Qa11.

Definition nat_of_qarity qa :=
  match qa with
  | Qa5  => 5
  | Qa6  => 6
  | Qa7  => 7
  | Qa8  => 8
  | Qa9  => 9
  | Qa10 => 10
  | Qa11 => 11
  end.

Coercion nat_of_qarity : qarity >-> nat.

Definition qarity_of_nat (n : nat) : qarity :=
  match n with
  | 5 => Qa5
  | 6 => Qa6
  | 7 => Qa7
  | 8 => Qa8
  | 9 => Qa9
  | 10 => Qa10
  | _ => Qa11
  end.

Lemma qarity_of_qarity (qa : qarity) : qarity_of_nat qa = qa.
Proof. by case: qa. Qed.

(* We specialize the question tree constructor according to the presence    *)
(* of left and right branches. We also need skewed left and right branches, *)
(* for configurations whose interior has an articulation.                   *)

Inductive question :=
  | Qask0
  | Qask1  of qarity
  | QaskL  of qarity & question
  | QaskR  of qarity & question
  | QaskLR of qarity & question & question
  | QaskLL of qarity & question
  | QaskRR of qarity & question.

Definition isQaskR q := if q is QaskR _ _ then true else false.

Fixpoint flatq q : seq nat :=
  match q with
  | Qask0           => [::]
  | Qask1 qa        => [:: qa : nat]
  | QaskL qa ql     => (qa : nat) :: flatq ql
  | QaskR qa qr     => (qa : nat) :: flatq qr
  | QaskLR qa ql qr => (qa : nat) :: flatq ql ++ flatq qr
  | QaskLL qa qll   => (qa : nat) :: flatq qll
  | QaskRR qa qrr   => (qa : nat) :: flatq qrr
  end.

(* Mirror image questions. *)

Fixpoint flipq q :=
  match q with
  | QaskL qa ql     => QaskR qa (flipq ql)
  | QaskR qa qr     => QaskL qa (flipq qr)
  | QaskLR qa ql qr => QaskLR qa (flipq qr) (flipq ql)
  | QaskLL qa qll   => QaskRR qa (flipq qll)
  | QaskRR qa qrr   => QaskLL qa (flipq qrr)
  | _               => q
  end.

Definition qstepL (G : hypermap) (x : G) := node (edge (node x)).
Definition qstepR (G : hypermap) (x : G) := node (edge x).

CoInductive quiz := Quiz of question & question.

Definition isQuizR qz := let: Quiz q0 q1 := qz in isQaskR q0 && isQaskR q1.

Definition flatqz qz := let: Quiz q0 q1 := qz in flatq q0 ++ flatq q1.

Definition flipqz qz :=
  if qz is Quiz (QaskR qa0 q01) (QaskR qa1 q10) then
    Quiz (QaskR qa0 (flipq q10)) (QaskR qa1 (flipq q01))
  else qz.

Section FitQuiz.

Variable G : hypermap.

Fixpoint walkq (x : G) q :=
  match q with
  | Qask0 => [::]
  | Qask1 qa => [:: x]
  | QaskL qa ql => x :: walkq (qstepL x) ql
  | QaskR qa qr => x :: walkq (qstepR x) qr
  | QaskLR qa ql qr => x :: walkq (qstepL x) ql ++ walkq (qstepR x) qr
  | QaskLL qa qll =>
    let xl := qstepL x in edge (node xl) :: walkq (qstepL xl) qll
  | QaskRR qa qrr => let xr := qstepR x in xr :: walkq (qstepR xr) qrr
  end.

Definition fitq x q := flatq q == map arity (walkq x q).

Lemma size_walkq x q : size (walkq x q) = size (flatq q).
Proof. by elim: q x => //= *; rewrite ?size_cat; congr _.+1; auto. Qed.

Lemma fitq_cat x q sa s :
 (flatq q ++ sa == map arity (walkq x q ++ s))
   = fitq x q && (sa == map arity s).
Proof.
rewrite /fitq; have /eqP := size_walkq x q.
elim: {q x}(walkq x q) (flatq q) => [|x s1 IHs1] [|n s1a] //= eq_sza.
by rewrite !eqseq_cons -andbA IHs1.
Qed.

Lemma size_flipq q :size (flatq (flipq q)) = size (flatq q).
Proof. elim: q => //= *; rewrite ?size_cat 1?addnC; congr _.+1; auto. Qed.

Definition walkqz x qz :=
  let: Quiz q0 q1 := qz in walkq x q0 ++ walkq (edge x) q1.

Lemma size_walkqz x qz : size (walkqz x qz) = size (flatqz qz).
Proof. by case: qz => q0 q1 /=; rewrite /= !size_cat !size_walkq. Qed.

Definition fitqz x qz := flatqz qz == map arity (walkqz x qz).

End FitQuiz.

Lemma fitqz_flip G x qz :
    plain_cubic G -> isQuizR qz ->
  @fitqz G x (flipqz qz) = @fitqz (mirror G) (face x) qz.
Proof.
case: qz => [] [] // qa0 q01 [] //= qa1 q10 [plainG cubicG] _.
move Dh: (fun y : G => y : mirror G) => h.
rewrite (congr1 (fun f => f (face x)) Dh); move: x.
have [e2 n3] := (plain_eq plainG, cubic_eq cubicG).
have nFh: {mono h : x / arity x} by move=> x; rewrite -Dh arity_mirror.
have hL: {morph h : x / qstepR x >-> qstepL x}.
  move=> x; rewrite -Dh /= (f_finv nodeI) -{2}[x]e2 -[edge x]n3 nodeK.
  by rewrite (finv_f nodeI).
have hR: {morph h : x / qstepL x >-> qstepR x}.
  by move=> x; rewrite hL -Dh /qstepL /qstepR /= (finv_f nodeI).
have{Dh} hE x: edge (h (face x)) = h (face (edge x)).
  by rewrite -Dh /= -{1}[x]e2 edgeK.
have nFen G1 x: arity (@edge G1 (node x)) = arity x.
  by rewrite -arity_face nodeK.
move: (mirror G) => G1 in h nFh hL hR hE *.
have fit_flip q x: fitq x (flipq q) = fitq (h x) q.
  rewrite /fitq; elim: q x => //= *; rewrite -?hL -?hR ?nFen nFh //;
    rewrite !eqseq_cons ?fitq_cat /fitq; try congr (_ && _); try by [].
  by rewrite /fitq andbC; congr (_ && _).
move=> x; rewrite /fitqz /= !eqseq_cons !fitq_cat /= !eqseq_cons hE !nFh.
rewrite !arity_face -!hR !(andbCA (fitq _ _)); congr [&& _, _ & _].
rewrite -fit_flip fit_flip andbC; congr (_ && _); congr (_ == map _ _).
  by rewrite /qstepR /qstepL e2 faceK.
by rewrite /qstepL edgeK.
Qed.

Section QuizEmbedding.

(* The main result of this library: the construction of a preembedding of a   *)
(* configuration map Gc into a plain cubic hypermap Gm from a quiz valid for  *)
(* Gc that also fits into Gm.                                                 *)

Variables (Gm Gc : hypermap) (rc : seq Gc).
Local Notation ac := (kernel rc).
Local Notation bc := [predC rc].
Let ac_bc : {subset ac <= bc} := subsetP (kernel_off_ring rc).
Let acF := kernelF rc.

Hypotheses (geoGm : plain_cubic Gm) (geoGc : plain_quasicubic rc).
Let e2m := plain_eq geoGm.
Let n3m := cubic_eq geoGm.
Let e2c := plain_eq geoGc.
Let n3c := quasicubic_eq geoGc.

Variables (x0m : Gm) (x0c : Gc) (qz : quiz).
Let s0c : seq Gc := walkqz x0c qz.
Let s0m : seq Gm := walkqz x0m qz.

Definition valid_quiz :=
  [/\ isQuizR qz, fitqz x0c qz, simple s0c & fband s0c =i ac].

Hypotheses (qz_ok : valid_quiz) (qz_x0m : fitqz x0m qz).

Definition embedqz x :=
  let i := find (cface x) s0c in
  iter (findex face (nth x0c s0c i) x) face (nth x0m s0m i).

Local Notation h := embedqz.
Local Notation hc  := (edge_central h).
Let hcE : {mono edge : x / x \in hc} := edge_central_edge h geoGc geoGm.

Let Dhx0 : h x0c = x0m.
Proof.
have [qz_R _ _ _] := qz_ok; rewrite /h /s0c /s0m.
by case: qz qz_R => [[] //= *]; rewrite connect0 findex0.
Qed.

Let Dhs0 i : h (nth x0c s0c i) = nth x0m s0m i.
Proof.
have [le_s0i | lt_is0] := leqP (size s0c) i.
  by rewrite !nth_default ?Dhx0 //; rewrite !size_walkqz in le_s0i *.
set x := nth _ s0c i; rewrite /h.
suffices ->: find (cface x) s0c = i by rewrite -/x findex0.
have[_ _ Us0F _] := qz_ok; have Us0 := simple_uniq Us0F.
have s0x: x \in s0c by apply: mem_nth.
rewrite -(index_uniq x0c lt_is0 Us0) -[nth _ _ i](simple_fproj Us0F s0x).
by rewrite index_uniq // -has_find; apply/hasP; exists x.
Qed.

Let Dhex0 : h (edge x0c) = edge x0m.
Proof.
have [qz_R _ _ _] := qz_ok; move: Dhs0 qz_R; rewrite /s0c /s0m.
case: qz => /= q0 q1 /(_ (size (flatq q0))).
by rewrite !nth_cat !size_walkq /= ltnn subnn andbC; case: q1.
Qed.

Lemma embedqz_arity x : x \in ac -> arity (h x) = arity x.
Proof.
have [_ /eqseqP qz_x0c _ <-] := qz_ok; rewrite /h => s0cFx.
set i := find (cface x) s0c; set y := nth x0c s0c i; set j := findex face y x.
have lti: i < size s0c by rewrite -has_find.
have s0_y: y \in s0c by apply: mem_nth.
have xFy: cface x y by apply: nth_find.
rewrite (arity_cface xFy) /y -(nth_map x0c 0) // -qz_x0c (eqseqP qz_x0m) -/s0m.
rewrite (nth_map x0m); last by rewrite !size_walkqz in lti *.
by elim: j => //= j <-; rewrite arity_face.
Qed.

Lemma embedqz_face : {in ac, {morph h : x / face x}}.
Proof.
move=> x ac_x; have [_ _ _ Dac] := qz_ok; rewrite /h -(eq_find (cface1 x)).
set i := find _ s0c; rewrite -Dhs0; set yc := nth _ s0c i.
have s0cFx: x \in fband s0c by rewrite Dac.
have ycFx: cface yc x by rewrite cfaceC (nth_find _ s0cFx).
rewrite -{1}(iter_findex ycFx) -!iterS.
have:= findex_max ycFx; rewrite leq_eqVlt.
case/predU1P=> [-> | /findex_iter->//]; rewrite (iter_order faceI) findex0 /=.
by rewrite -embedqz_arity ?(iter_order faceI) ?(closed_connect acF ycFx).
Qed.

Lemma embedqz_central : {subset s0c <= hc}.
Proof.
have hc_walk x q: let s := walkq (node x) q in
     x \in ac -> edge x \in ac -> x \in hc ->
     all (mem ac) s -> map h s == walkq (node (h x)) q ->
  all hc s.
- elim: q x => //= _.
  + move=> x ax_c _ _ _ /andP[/eqP hnx _].
    by rewrite andbT -(inj_eq faceI) hnx -embedqz_face 1?(fclosed1 acF) ?nodeK.
  + move=> q IHq x ac_x ac_ex /eqP hex /andP[ac_nx ac_q].
    rewrite eqseq_cons => /andP[/eqP hnx h_q].
    have ac_enx: edge (node x) \in ac by rewrite (fclosed1 acF) nodeK.
    have ac_ennx: edge (node (node x)) \in ac by rewrite (fclosed1 acF) nodeK.
    have hc_nx: node x \in hc.
      by rewrite inE hnx -{2}[x]nodeK embedqz_face ?faceK ?eqxx.
    have hc_ennx: edge (node (node x)) \in hc.
      rewrite inE e2c {1}(canRL nodeK (n3c (ac_bc ac_x))).
      rewrite embedqz_face // hex -(canRL nodeK (n3m _)).
      by rewrite (canRL edgeK (e2m _)) -embedqz_face // nodeK hnx.
    rewrite [_ == _]hc_nx /qstepL IHq //.
      by rewrite e2c (canRL nodeK (n3c (ac_bc ac_x))) -fclosed1.
    by rewrite -[h (edge _)]faceK -embedqz_face // nodeK hnx.
  + move=> q IHq x ac_x ac_ex /eqP hex /andP[ac_nx ac_q].
    rewrite eqseq_cons => /andP[/eqP hnx h_q].
    have ac_enx: edge (node x) \in ac by rewrite (fclosed1 acF) nodeK.
    have ac_ennx: edge (node (node x)) \in ac by rewrite (fclosed1 acF) nodeK.
    have hc_nx: node x \in hc.
      by rewrite inE hnx -{2}[x]nodeK embedqz_face ?faceK ?eqxx.
    by rewrite [_ == _]hc_nx /qstepR IHq ?e2c ?hcE // (eqP hc_nx) hnx.
  + move=> ql IHql qr IHqr x ac_x ac_ex /eqP hex /andP[ac_nx].
    rewrite !all_cat eqseq_cons map_cat eqseq_cat ?size_map ?size_walkq //.
    case/andP=> ac_ql ac_qr /and3P[/eqP hnx h_ql h_qr].
    have ac_enx: edge (node x) \in ac by rewrite (fclosed1 acF) nodeK.
    have ac_ennx: edge (node (node x)) \in ac by rewrite (fclosed1 acF) nodeK.
    have hc_nx: node x \in hc.
      by rewrite inE hnx -{2}[x]nodeK embedqz_face ?faceK ?eqxx.
    have hc_ennx: edge (node (node x)) \in hc.
      rewrite inE e2c {1}(canRL nodeK (n3c (ac_bc ac_x))).
      rewrite embedqz_face // hex -(canRL nodeK (n3m _)).
      by rewrite (canRL edgeK (e2m _)) -embedqz_face // nodeK hnx.
    rewrite [_ == _]hc_nx /= /qstepL /qstepR IHql // ?IHqr // ?e2c ?hcE //.
    * by rewrite (eqP hc_nx) hnx.
    * by rewrite (canRL nodeK (n3c (ac_bc ac_x))) -fclosed1.
    by rewrite -[h (edge _)]faceK -embedqz_face // nodeK hnx.
  - move=> q IHq x ac_x ac_ex /eqP hex /andP[ac_enLnx ac_q].
    rewrite eqseq_cons => /andP[/eqP henLnx h_q].
    have ac_fex: face (edge x) \in ac by rewrite -fclosed1.
    have ac_ffex: face (face (edge x)) \in ac by rewrite -fclosed1.
    have hc_enLnx: edge (node (qstepL (node x))) \in hc.
      rewrite inE e2c henLnx /qstepL !(canRL nodeK (n3m _)) !e2m.
      rewrite (canRL nodeK (n3c (ac_bc ac_x))) (canRL edgeK (e2c _)).
      by rewrite (n3c (ac_bc _ )) // !embedqz_face // hex.
    rewrite [_ == _]hc_enLnx {1}/qstepL IHq ?henLnx //.
    by rewrite e2c -[x]edgeK /qstepL (canRL edgeK (e2c _)) !(n3c (ac_bc _)).
  - move=> q IHq x ac_x ac_ex /eqP hex /andP[ac_Rnx ac_q].
    rewrite eqseq_cons => /andP[/eqP hRnx h_q].
    have ac_enx: edge (node x) \in ac by rewrite (fclosed1 acF) nodeK.
    have ac_enenx:  edge (node (edge (node x))) \in ac.
      by rewrite (fclosed1 acF) nodeK.
    have hc_Rnx: qstepR (node x) \in hc.
      by rewrite inE hRnx /qstepR -!(canF_eq faceK) -!embedqz_face ?nodeK.
    by rewrite [_ == _]hc_Rnx {1}/qstepR IHq ?e2c ?hcE // (eqP hc_Rnx) hRnx.
have hc_x0: x0c \in hc by rewrite inE Dhx0 Dhex0.
have hc_ex0: edge x0c \in hc by rewrite hcE.
have [qzR _ _ Dac] := qz_ok.
have s0_ac: s0c \subset ac by rewrite -(eq_subset_r Dac) ring_fband.
have{Dac} Ehs0: map h s0c == s0m.
  apply/eqP; pose n := size (flatqz qz).
  have [Dnc Dnm]: size s0c = n /\ size s0m = n by rewrite !size_walkqz.
  rewrite -(take_size s0c) -(take_size s0m) Dnc Dnm.
  elim: {-2}n (leqnn n) => [|i IHi] lt_i_n; first by rewrite !take0.
  rewrite (take_nth x0c) ?Dnc // map_rcons Dhs0 (IHi (ltnW _)) //.
  by rewrite -take_nth // Dnm.
apply: subsetP; move: s0_ac Ehs0; rewrite /s0c /s0m !subset_all.
case: qz qzR => [] []//= _ q01 []//= _ q10 _; rewrite hc_x0 !all_cat map_cat /=.
rewrite hc_ex0 !(eqseq_cons, eqseq_cat); last by rewrite size_map !size_walkq.
case/and4P=> ac_x0 ac_q01 ax_ex0 ac_q10 /and4P[/eqP<- h_q01 /eqP<- h_q10].
rewrite /qstepR !hc_walk // ?e2c // ?(eqP hc_x0) //.
by rewrite /qstepR (eqP hc_x0) e2c e2m in h_q10.
Qed.

Lemma embedqz_rlinked : rlink_connected [predI ac & hc].
Proof.
have ccRfband x a:
    x \in fband a -> rlink_connected [predI fband a & hc] -> node x \in hc ->
  rlink_connected [predI fband (rcons a (node x)) & hc].
- move=> aFx ccFa hc_nx y z; rewrite !inE -!rot1_cons !fband_rot !fband_cons.
  have aFenx: edge (node x) \in [predI fband a & hc].
    by rewrite inE /= (fclosed1 (fbandF a)) nodeK aFx hcE.
  case yFnx: (cface y (node x)) => [] => [_ | {yFnx}].
    case zFnx: (cface z (node x)) => [] => [_ | {zFnx}].
      by exists [::]; rewrite //= /rlink faceK (same_cface yFnx) cfaceC zFnx.
    case/(ccFa _ _ aFenx)=> p; rewrite edgeK=> nxRp aFp.
    exists (node x :: p); first by rewrite /= {1}/rlink faceK yFnx.
    rewrite /= fband_rot fband_cons connect0 hc_nx; apply: sub_all aFp => t /=.
    by rewrite fband_rot fband_cons andb_orl orbC => ->.
  case zFnx: (cface z (node x)) => [] => [|{zFnx}].
    case/ccFa/(_ aFenx)=> p nfyRp aFp _; exists (rcons p (edge (node x))).
      by rewrite rcons_path nfyRp last_rcons /= /rlink e2c cfaceC zFnx.
    rewrite all_rcons /= fband_rot fband_cons andb_orl orbC [l in l || _]aFenx.
    apply: sub_all aFp => t /=; rewrite fband_rot fband_cons andb_orl => ->.
    exact: orbT.
  move/ccFa=> ccFay /ccFay[p nfyRp aFp]; exists p => //.
  apply: sub_all aFp => t /=; rewrite fband_rot fband_cons andb_orl => ->.
  exact: orbT.
have ccRwalk x a q: let s := walkq (node x) q in
    x \in fband a -> edge x \in fband a -> all (mem ac) a ->
    rlink_connected [predI fband a & hc] -> all [predI ac & hc] s ->
  rlink_connected [predI fband (a ++ s) & hc].
- elim: q x a => /=; try by move=> *; rewrite cats0.
  + by move=> _ x a ? _ _ ?; rewrite andbT cats1 => /andP[_]; apply: ccRfband.
  + move=> _ ql IHql x a aFx aFex a_ac ccRa /andP[/andP[ac_nx hc_nx] ac_ql].
    rewrite -cat_rcons /qstepL; apply: IHql => //; last exact: ccRfband.
    * by rewrite -rot1_cons fband_rot fband_cons cface1 nodeK connect0.
    * rewrite e2c -2!(nodeK (node (node _))) (n3c (ac_bc ac_nx)) nodeK.
      by rewrite -cats1 fband_cat -(fclosed1 (fbandF a)) aFex.
    by rewrite all_rcons /= ac_nx.
  + move=> _ qr IHqr x a aFx _ a_ac ccRa /andP[/andP[ac_nx hc_nx] ac_qr].
    rewrite -cat_rcons /qstepR; apply: IHqr => //; last exact: ccRfband.
    * by rewrite -cats1 fband_cat (fclosed1 (fbandF a)) nodeK aFx.
    * by rewrite e2c -rot1_cons fband_rot fband_cons connect0.
    by rewrite all_rcons /= ac_nx.
  + move=> _ ql IHql qr IHqr x a aFx aFex a_ac ccRa.
    rewrite all_cat => /and3P[/andP[ac_nx hc_nx] ac_ql ac_qr].
    rewrite -cat_rcons catA /qstepR; apply: IHqr => //. 
    * by rewrite cat_rcons fband_cat (fclosed1 (fbandF a)) nodeK aFx.
    * by rewrite e2c cat_rcons fband_cat fband_cons connect0 orbT.
    * rewrite cat_rcons all_cat a_ac /= ac_nx /=.
      by move: ac_ql; rewrite all_predI => /andP[].
    rewrite /qstepL; apply: IHql => //; last exact: ccRfband.
    * by rewrite -rot1_cons fband_rot fband_cons cface1 nodeK connect0.
    * rewrite e2c -2!(nodeK (node (node _))) (n3c (ac_bc ac_nx)) nodeK.
      by rewrite -(fclosed1 (fbandF _)) -cats1 fband_cat aFex.
    by rewrite all_rcons /= ac_nx.
  + move=> _ qll IHq x a _ aFex a_ac ccRa /andP[/andP[ac_neLnx hc_neLnx] ac_q].
    have ac_fex: face (edge x) \in ac.
      have [y /(allP a_ac)/=ac_y exFy] := hasP aFex.
      by rewrite -fclosed1 // (closed_connect acF exFy).
    have ac_ffex: face (face (edge x)) \in ac by rewrite -fclosed1.
    have Dffex: node (qstepL (node x)) = face (face (edge x)).
      rewrite /qstepL -{1}[x]edgeK (n3c (ac_bc ac_fex)).
      by rewrite (canRL edgeK (e2c _)) (n3c (ac_bc _)).
    rewrite -cat_rcons {2}/qstepL; apply: IHq => //.
    * by rewrite -rot1_cons fband_rot fband_cons connect0.
    * by rewrite e2c Dffex -cats1 fband_cat -!(fclosed1 (fbandF a)) /= aFex.
    * by rewrite all_rcons /= ac_neLnx.
    rewrite Dffex (canRL edgeK (e2c _)) in hc_neLnx *; apply: ccRfband => //.
    by rewrite -!(fclosed1 (fbandF a)).
  move=> _ qrr IHq x a aFx _ a_ac ccRa /andP[/andP[ac_Rnx hc_Rnx] ac_q].
  have ac_enx: edge (node x) \in ac.
    have [y /(allP a_ac)/=ac_y xFy] := hasP aFx.
    by rewrite (fclosed1 acF) nodeK (closed_connect acF xFy).
  rewrite -cat_rcons {2}/qstepR; apply: IHq => //.
  * by rewrite 2!(fclosed1 (fbandF _)) /qstepR !nodeK -cats1 fband_cat aFx.
  * by rewrite e2c -rot1_cons fband_rot fband_cons connect0.
  * by rewrite all_rcons /= ac_Rnx.
  rewrite /qstepR; apply: ccRfband => //.
  by rewrite (fclosed1 (fbandF a)) nodeK.
have [qzR _ _ Dac] := qz_ok.
have: all [predI ac & hc] s0c.
  apply/allP=> y s0c_y /=; rewrite embedqz_central //.
  by rewrite -Dac (subsetP (ring_fband _)).
move: qzR Dac; rewrite /s0c; case: qz => q0 q1 /=; rewrite all_cat /=.
case: q0 => //= [_ q01]; case: q1 => //= [_ q10] _ Dac.
case/and3P=> /andP[/andP[ac_x0 hc_x0] ac_q01] /andP[ac_ex0 hc_ex0] ac_q10.
pose a := [:: x0c; edge x0c] ++ walkq (qstepR x0c) q01.
pose a2 := a ++ walkq (qstepR (edge x0c)) q10.
have ccRa2: rlink_connected [predI fband a2 & hc].
  apply: (ccRwalk); rewrite // ?e2c //.
  - by rewrite fband_cons connect0.
  - by rewrite !fband_cons connect0 orbT.
  - by move: ac_q01; rewrite /= ac_x0 ac_ex0 all_predI => /andP[].
  apply: (ccRwalk); rewrite // ?e2c //= ?fband_cons ?connect0 ?orbT //.
    by rewrite ac_x0 ac_ex0.
  rewrite -cat1s cats1 -{2}[x0c]faceK e2c; apply: ccRfband => //.
  - by rewrite fband_cons cfaceC fconnect1.
  - move=> x y; rewrite !inE !fband_cons !orbF => /andP[xFx0 _] /andP[yFx0 _].
    by exists [::]; rewrite //= /rlink faceK (same_cface xFx0) cfaceC yFx0.
  by rewrite -{1}[x0c]e2c edgeK.
have{Dac} Dac: ac =i fband a2.
  by move=> x; rewrite -Dac !(fband_cons, fband_cat); do !bool_congr.
move=> x y; rewrite !(Dac, inE) => a2Fx a2Fy.
have [p nfxRp a2_p] := ccRa2 _ _ a2Fx a2Fy.
by exists p => //; apply: sub_all a2_p => z; rewrite inE /= Dac.
Qed.

Lemma quiz_preembedding : preembedding ac h.
Proof.
split; last exact: embedqz_rlinked.
- exact: embedqz_face.
- exact: embedqz_arity.
have [_ _ _ Dac] := qz_ok.
apply/subsetP=> x; rewrite -Dac => /hasP[y s0_y xFy].
by apply/exists_inP; exists y => //=; apply: embedqz_central.
Qed.

End QuizEmbedding.
