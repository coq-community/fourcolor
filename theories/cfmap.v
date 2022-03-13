(* (c) Copyright 2006-2018 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import fintype path fingraph.
From fourcolor Require Import hypermap geometry color.

(******************************************************************************)
(*   Configuration maps are entered as little linear construction programs:   *)
(* starting from a basic triangle, these build a sequence of concentric quasi *)
(* cubic maps, alternatively rotating the perimeter and adding a single outer *)
(* node (and a new region) or two adjacent ones (which close up a region and  *)
(* start a new one).                                                          *)
(*   We also need two generalizations of this construction:                   *)
(*    - the proof of the Birkhoff theorem requires computing the coloring of  *)
(*      a few non two-connected quasi cubic plain maps; they can be obtained  *)
(*      by starting the construction from a single edge, and allowing adding  *)
(*      a disconnected face during the construction.                          *)
(*    - the contract colorings are computed as colorings of reduced maps      *)
(*      whose construction is similar to the above, but uses two operations   *)
(*      that close a region by either merging its two neighbors (creating a   *)
(*      binary node), or making them adjacent (creating a ternary node).      *)
(* Defined here:                                                              *)
(*     cpstep == type of basic steps in a the config construction programs.   *)
(*               There are 7 constructors: CpR n, cpR', CpY, CpH, CpU, CpK,   *)
(*               and CpA (see below); CpR is a coercion from nat.             *)
(*               The R and R' steps merely rotate the start point of the      *)
(*               configuration around its perimeter; note that there is no    *)
(*               constructor for the N step, which is just a rotation         *)
(*               conjugate of the K step.                                     *)
(*      cprog == the type of configuration programs (= seq cpstep). The       *)
(*               actual construction is performed right-to-left.              *)
(*     config == the type of configuration descriptors, which add symmetry    *)
(*               and contract annotations to a configuration program. The two *)
(*               annotations are documented in libraries cfquiz and           *)
(*               cfcontract, respectively, which make use of them.            *)
(*   cfsym cf == the (boolean) symmetry annotation of cf : config.            *)
(* cfcontract cf == the contract annotation of cf : config.                   *)
(*  cfprog cf == the configurartion construction program of cf : config.      *)
(*   cubic_prog cp <=> cp : cprog consists only of R, U, Y and H steps.       *)
(*  config_prog cp <=> cp : cprog consists only of R, Y and H steps, and ends *)
(*               with a Y step (so the construction starts with a Y step).    *)
(* pointed_map == record type bundling a hypermap (pointee) with a reference  *)
(*               point (pointer). Both pointee and pointer are coercions.     *)
(*   cpring x == the ring (reverse N-cycle) of the remainder hypermap of a    *)
(*               configuration, given a reference point on that ring; unless  *)
(*               it is trivial, cpring x will start with node x :: x :: ...   *)
(* proper_cpring x <=> x != node x, so cpring x is nontrivial (of size > 1).  *)
(* long_cpring x <=> face (edge x) != node x, so cpring x has size > 2.       *)
(*   Given a reference dart x in a hypermap G, we provide pointed maps that   *)
(* implement the various construction steps, along with injections from G:    *)
(*   ecpR n x == the pointed_map with reference dart node^-n x, which         *)
(*               implements an R n step at dart x.                            *)
(*     ecpA x == a pointed_map that implements an A step at x.                *)
(*     ecpU x == a pointed_map that implements a U step at x.                 *)
(*     ecpN x == a pointed_map that implements an N step at x.                *)
(*    ecpR' x == a pointed_map that implements an R' step at x.               *)
(*            := ecpR (order node x).-1 x                                     *)
(*     ecpK x == a pointed_map that implements a K step at x.                 *)
(*            := ecpR 1 (ecpN (ecpR' x))                                      *)
(*     ecpY x == a pointed_map that implements a Y step at x = ecpN (ecpU x). *)
(*     ecpH x == a pointed_map that implements an H step at x = ecpN (ecpY x).*)
(*  icpR n x, icpR' x, icpA x, icpU x, icpN x, icpK x, icpY x, icpH x         *)
(*            == injections from G into the above maps; the first three are   *)
(*               actually identity functions as the hypermap is unchanged.    *)
(*   cpmap cp == the pointed_map obtained by running cp : cprog right-to-left.*)
(*   cfmap cf == the pointed_map of cf : config (= cpmap (cfprog cf)).        *)
(*  cfring cf == the ring of cf : config (= cpring (cfmap cf)).               *)
(*   cpker cp == a seq of darts transversal of the kernel of cpmap cp, with   *)
(*               one dart for each face NOT incident to the ring of cpmap cp. *)
(*               Thus, cpring (cpmap cp) ++ cpker cp is a transversal of the  *)
(*               faces of cpmap cp.                                           *)
(* @injcp cp1 cp1 == injection from cpmap cp2 to cpmap (catrev cp1 cp2).      *)
(* cprsize cp == size of the ring cpring (cpmap cp).                          *)
(*     cfmask == a pair of bitseq's used to select faces in a configurations. *)
(* cpmask cm cp == the subsequence of cpring (cpmap cp) ++ cpker cp selected  *)
(*               by cm : cfmask.                                              *)
(*  cpadj cm cp == a cfmask selecting the set of faces adjacent to the set of *)
(*               faces of cpmap cp selected by cm : cfmask; this assumes cp   *)
(*               has only H, Y and R steps.                                   *)
(* Import ConfigSyntax :: activates the concrete syntax for configuration     *)
(*               programs and specifications:                                 *)
(*    Cprog H 3 H 2 Y Y ::= [:: CpH; CpR 3; CpH; CpR 2; CpY; CpY]             *)
(*    Config* 1 2 H 2 H Y ::=                                                 *)
(*        {|cfsym = true; cfcontract = [:: 1; 2]; cfprog = Cprog H 2 H Y|}    *)
(*    Config 1 H Y ::= {|cfsym = false; cfcontract = [:: 1]; cfprog = .. |}   *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive cpstep : Set :=
  | CpR of nat (* rotation around the outer ring (noop on overflow) *)
  | CpR'       (* single-step reverse rotation (for encodings)      *)
  | CpY        (* new Y junction and face                           *)
  | CpH        (* new H junction and face (closing an inner face)   *)
  | CpU        (* new face, no junctions (U-shaped loop)            *)
  | CpK        (* new K (inverted Y) junction (closing off a face)  *)
  | CpA.       (* inverted-V junction, merging neighbors of a face  *)

(* A configuration map construction program is just a sequence of steps.     *)
(* It is interpreted RIGHT TO LEFT, starting from a simple U-shaped map.     *)

Definition cprog := seq cpstep.

Fixpoint cubic_prog (cp : cprog) :=
  match cp with
  | [::] => true
  | CpR _ :: cp' => cubic_prog cp'
  | CpU :: cp' => cubic_prog cp'
  | CpY :: cp' => cubic_prog cp'
  | CpH :: cp' => cubic_prog cp'
  | _ => false
  end.

(******************************************************************************)
(*   The configuration data comprises the construction program for the        *)
(* configuration map, the reducibility contract, represented as a sequence of *)
(* integers (indexing the contract edges in the construction process), and a  *)
(* boolean flagging symmetrical maps, whose reflection does not need to be    *)
(* checked when scanning a part for reducible patterns (see quiztree).        *)
(*   The reducibility program aways starts with an H, and ends with a Y; we   *)
(* need to check this explicitly (both in cfquiz.v and cfcontract.v). The     *)
(* initial H signals the end of the contract in the concrete syntax. The      *)
(* pattern-matching tree store further assumes that if a face has arity 9,    *)
(* 10, or 11, it is the one containing the first dart created.                *)
(******************************************************************************)

Record config := ConfigRecord {
  cfsym : bool;
  cfcontract_ref : seq nat;
  cfprog : cprog
}.

Fixpoint config_prog (cp : cprog) :=
  match cp with
  | CpR _ :: cp' => config_prog cp'
  | [:: CpY] => true
  | CpY :: cp' => config_prog cp'
  | CpH :: cp' => config_prog cp'
  | _ => false
  end.

Lemma config_prog_cubic cp : config_prog cp -> cubic_prog cp.
Proof. by elim: cp => [|[]] //= []. Qed.

Module ConfigSyntax.

Definition H := CpH.
Definition Y := CpY.
Definition U := CpU.
Coercion CpR : nat >-> cpstep.

Definition cons_cp : cpstep -> cprog -> cprog := cons.

Notation "'Cprog' s1 .. sn" :=
  (cons_cp s1 .. (cons_cp sn [::]) .. )
  (at level 100, s1, sn at level 8, format "'Cprog'  s1  ..  sn").

Notation "'Cprog'" := ([::] : cprog) (at level 100).

Fixpoint parse_config sym cc (cp : cprog) {struct cp} : config :=
  if cp is CpR i :: cp' then parse_config sym (i :: cc) cp' else
  ConfigRecord sym (rev cc) cp.

Notation "'Config' * s1 .. sn" :=
  (parse_config true [::] (cons_cp s1 .. (cons_cp sn [::]) .. ))
  (at level 100, s1, sn at level 8, format "'Config' *  s1  ..  sn").
Notation "'Config' s1 .. sn" :=
  (parse_config false [::] (cons_cp s1 .. (cons_cp sn [::]) .. ))
  (at level 100, s1, sn at level 8, format "'Config'  s1  ..  sn").

End ConfigSyntax.

Module ConfigSamples.

(* Samples: the pentaton map construction, and the first reducible config.   *)

Import ConfigSyntax.

Section Samples.

Let pentamap := Cprog H 4 Y Y.
Let config1 := Config* 15 H 3 H 5 H 5 Y 4 H 4 Y 2 Y 1 Y.

(* Eval Compute in (config_prog (cfprog config1)). *)

End Samples.
End ConfigSamples.

Record pointed_map := PointedMap {pointee :> hypermap; pointer :> pointee}.

Arguments PointedMap : clear implicits.

Section CpRing.

Variables (G : hypermap) (x0 : G).

Definition cpring := rev (orbit node (node (node x0))).

Definition proper_cpring := x0 != node x0.
Definition long_cpring := face (edge x0) != node x0.

Lemma cpring_uniq : uniq cpring.
Proof. by rewrite rev_uniq orbit_uniq. Qed.

Lemma mem_cpring x : (x \in cpring) = cnode x0 x.
Proof. by rewrite mem_rev -fconnect_orbit -!cnode1. Qed.

Lemma size_cpring : size cpring = order node x0.
Proof. by rewrite -(card_uniqP cpring_uniq) (eq_card mem_cpring). Qed.

Lemma size_proper_cpring : proper_cpring = (1 < size cpring).
Proof.
move: (iter_order nodeI x0) (orbit_uniq node x0).
rewrite size_cpring /proper_cpring /orbit -(orderSpred node x0).
by case: _.-1 => /= [-> | n _ /andP[/norP[]] //]; rewrite eqxx.
Qed.

Lemma size_long_cpring : long_cpring = (2 < size cpring).
Proof.
move: (orderSpred node x0) (iter_order nodeI x0) (orbit_uniq node x0).
rewrite size_cpring /long_cpring (canF_eq (canF_sym nodeK)) /orbit.
case: (order node x0) => [|[|[|n]]] //= _ Dnx; try by rewrite !Dnx eqxx.
by case/andP => /norP[_ /norP[]].
Qed.

Lemma cycle_rev_cpring : fcycle node (rev cpring).
Proof. by rewrite /cpring revK (cycle_orbit nodeI). Qed.

Lemma ucycle_rev_cpring : ufcycle node (rev cpring).
Proof. by rewrite /ucycle rev_uniq cpring_uniq cycle_rev_cpring. Qed.

Lemma cpring_def p :
    (if p is x :: _ then x = node x0 else False) ->
  ufcycle node (rev p) -> cpring = p.
Proof.
case Dp: {1}p => // [x p'] Dx /andP[cycNp Up]; rewrite {x}Dx in Dp.
have{Up} Dn: size (rev p) = order node (node (node x0)).
  have p_nx0: node x0 \in rev p by rewrite mem_rev Dp mem_head.
  by rewrite (order_cycle cycNp Up) // -(fconnect_cycle cycNp p_nx0) fconnect1.
rewrite (cycle_path x0) {1}Dp rev_cons last_rcons in cycNp.
case/fpathP: cycNp => n Dp'; rewrite Dp' size_traject in Dn.
by rewrite /cpring /orbit -Dn -Dp' revK.
Qed.

Lemma head_cpring : cpring = node x0 :: behead cpring.
Proof.
rewrite /cpring /orbit -orderSpred /= lastI rev_rcons; congr (_ :: _).
by apply: nodeI; rewrite last_traject -iterS orderSpred (iter_order nodeI).
Qed.

Lemma head_long_cpring :
  long_cpring -> cpring = [:: node x0, x0, face (edge x0) & drop 3 cpring].
Proof.
move: cycle_rev_cpring; rewrite size_long_cpring head_cpring.
case: cpring => [|x' [|x [|y p]]] //= cycNp _; move: cycNp.
rewrite !rev_cons -!(rcons_cons, =^~ rot_cycle, rot1_cons) /= (inj_eq nodeI).
by rewrite drop0 (canF_eq nodeK) => /and3P[/eqP-> /eqP-> _].
Qed.

Lemma head_proper_cpring :
  proper_cpring -> cpring = [:: node x0, x0 & drop 2 cpring].
Proof.
case x0gt2: long_cpring; first by rewrite head_long_cpring.
rewrite size_proper_cpring leq_eqVlt -size_long_cpring x0gt2 orbF.
rewrite /cpring size_rev size_orbit /orbit => /eqP<-.
by move/eqP: x0gt2 => /(canRL (canF_sym nodeK)) <-.
Qed.

End CpRing.

Section ExtConfig.

Variables (n0 : nat) (G : hypermap) (x0 : G).

(* We list all the assumptions on G here so that they appear in the standard *)
(* order, but most of the lemmas below only depend on a few assumptions. In  *)
(* particular, the map constructions do not depend on any assumption on G.   *)

Hypotheses (planarG : planar G) (bridge'G : bridgeless G).
Hypotheses (plainG : plain G) (cubicG : quasicubic (rev (cpring x0))).
Hypotheses (ccG : connected G) (x0gt1 : proper_cpring x0).

Let geoG : ucycle_plain_quasicubic_connected (rev (cpring x0)).
Proof. by do ?split=> //; apply: ucycle_rev_cpring. Qed.

(* Reverse ring rotation; note that the map construction matches the ring   *)
(* rotation for arbitrary n0 (it is the identity if n0 >= (order node x0)). *)

Definition ecpR := PointedMap G (iter (order node x0 - n0) node x0).

Definition icpR (x : G) : ecpR := x.

Lemma cpring_ecpR : cpring (pointer ecpR) = rot n0 (cpring x0).
Proof.
apply: cpring_def; last first.
  by rewrite rev_rot rotr_ucycle; apply: ucycle_rev_cpring.
rewrite /cpring -rev_rotr /rotr size_orbit /=; set m := order _ _.
have <-: m = order node x0 by apply: eq_card => x; rewrite !inE -!cnode1.
case: (m - n0) (leq_subr n0 m) => [|n] Hn.
  by rewrite rot0 -/(cpring x0) head_cpring.
rewrite rev_cat (take_nth (node (node x0))) ?size_orbit ?rev_rcons //=.
by rewrite nth_traject // -!iterSr.
Qed.

Lemma size_cpring_ecpR : size (cpring (pointer ecpR)) = size (cpring x0).
Proof. by rewrite cpring_ecpR size_rot. Qed.

Lemma cubic_ecpR : quasicubic (rev (cpring ecpR)).
Proof.
apply: etrans cubicG; apply: eq_subset => x; congr (~~ _).
by rewrite /= cpring_ecpR 2!mem_rev mem_rot.
Qed.

(******************************************************************************)
(*   Merging neighbors; this trivially produces a plain graph, but otherwise  *)
(* it has very few properties; fortunately, we only need the preservation of  *)
(* face connectivity, since we only use the merge to build contract coloring  *)
(* maps. To make sure this property is always true, we must check whether the *)
(* neighbors are already merged, in which case we need to create a hyperedge  *)
(* to avoid the creation of a separate component.                             *)
(*    The merge operation breaks both the cface and edge relation, but in the *)
(* right direction for cface (the resulting map is more connected than the    *)
(* base one) and it preserves the adj relation, which is enough for coloring. *)
(******************************************************************************)

Definition ecpA_edge x :=
  if ~~ cface (edge x0) (node x0) then edge x else
  if x == x0 then edge (node (node x0)) else
  if x == node (node x0) then edge x0 else edge x.

Definition ecpA_node x :=
  if x == node x0 then x0 else
  if node x == x0 then node (node x0) else node x.

Definition ecpA_face x :=
  if cface (edge x0) (node x0) then face x else
  if x == edge x0 then node x0 else
  if face x == node x0 then face (edge x0) else face x.

Fact ecpA_subproof : cancel3 ecpA_edge ecpA_node ecpA_face.
Proof.
move=> x; rewrite /ecpA_edge /ecpA_face; case: ifP => ->; rewrite /= /ecpA_node.
  have [-> | /negPf x0'x] := altP (x =P x0); first by rewrite nodeK eqxx.
  rewrite -fun_if edgeK (canF_eq (canF_sym nodeK)).
  by have [<- | /negPf ->] := altP (x =P _); rewrite ?(eqxx, eq_sym x0) x0'x.
rewrite (inj_eq edgeI) -!fun_if !(canF_eq (canF_sym nodeK)).
have [-> | /negPf x0'x] := altP (x =P x0); first by rewrite eqxx.
rewrite edgeK (canF_eq (canF_sym nodeK)).
have [Dx | /negPf ->] := altP (x =P _); last by rewrite x0'x edgeK.
by rewrite eqxx -Dx eq_sym x0'x.
Qed.

Definition ecpA_map := Hypermap ecpA_subproof.

Definition ecpA := PointedMap ecpA_map (face (@edge ecpA_map (face (edge x0)))).

Definition icpA (x : G) : ecpA := x.

Lemma baseN_ecpA : fun_base icpA node node (pred2 (node x0) (face (edge x0))).
Proof.
by move=> x y; rewrite /icpA /= /ecpA_node (canF_eq nodeK); do 2?case: ifP.
Qed.

Lemma cpring_ecpA :
  cpring ecpA
     = (if long_cpring x0 then behead (behead (cpring x0)) else cpring x0).
Proof.
case x0gt2: (long_cpring x0).
  apply cpring_def; first by rewrite (head_long_cpring x0gt2) edgeK.
  apply/andP; split; last first.
    rewrite rev_uniq; have:= cpring_uniq x0; rewrite (head_long_cpring x0gt2).
    by case/and3P.
  move: (cycle_rev_cpring x0); rewrite (head_long_cpring x0gt2) /= !rev_cons.
  do 4![rewrite -rot1_cons rot_cycle -?rcons_cons] => /= /and3P[_ _].
  have nAfex0: ecpA_node (face (edge x0)) = node (node x0).
    by rewrite /ecpA_node -(inj_eq nodeI) edgeK eqxx; case: eqP.
  case Dp: (rev (drop 3 (cpring x0))) => [|x p]; rewrite /= nAfex0 //.
  rewrite -(map_path baseN_ecpA) ?map_id // belast_rcons has_predU !has_pred1.
  move: (cpring_uniq x0); rewrite (head_long_cpring x0gt2) -Dp !mem_rev /= !inE.
  by rewrite !negb_or => /and4P[/and3P[_ _ ->]].
apply cpring_def; first by move/eqP: x0gt2; rewrite head_cpring edgeK.
rewrite /ucycle rev_uniq /= cpring_uniq andbT.
move: x0gt2 (cycle_rev_cpring x0) (cpring_uniq x0).
rewrite size_long_cpring head_cpring /= /ecpA_node.
case: (behead _) => [|x[]] //= _; rewrite !andbT !eqxx (inj_eq nodeI) eq_sym //.
by case/andP=> /eqP-> _; rewrite inE eqxx andbT eq_sym => /negPf->.
Qed.

Definition sub2ifgt2 n := if n is n'.+3 then n'.+1 else n.

Lemma size_cpring_ecpA : size (cpring ecpA) = sub2ifgt2 (size (cpring x0)).
Proof.
rewrite cpring_ecpA /=; have [x0gt2|] :=boolP (long_cpring x0).
  by rewrite head_long_cpring.
by rewrite size_long_cpring; case: (size _) => [|[|[|n]]].
Qed.

Lemma baseF_ecpA :
  fun_base icpA face face (pred2 (edge x0) (edge (node (node x0)))).
Proof.
move=> x y; rewrite /icpA /= /ecpA_face => /norP[ex0'x ennx0'x].
by rewrite (negPf ex0'x) (canF_eq faceK) (negPf ennx0'x) if_same.
Qed.

Lemma ecpA_merge : cface (node ecpA) (node x0).
Proof.
rewrite edgeK /=; case ex0Fnx0: (cface (edge x0) (node x0)).
  by rewrite /ecpA_face ex0Fnx0 -cface1.
have: cface (node x0) (edge (node (node x0))) by rewrite cface1r nodeK.
case/connectP=> _ /shortenP[p nx0Fp Up _] Lp.
have:= nx0Fp; rewrite -(map_path baseF_ecpA) ?map_id => [{}nx0Fp|].
  rewrite (@cfaceC ecpA) (connect_trans (path_connect nx0Fp (mem_last _ _))) //.
  apply: connect1; rewrite -Lp /= /ecpA_face ex0Fnx0 nodeK eqxx.
  by rewrite (canF_eq (canF_sym faceK)); case: ifP.
move: Up; rewrite lastI -Lp rcons_uniq => /andP[p'ennx0 _].
rewrite has_predU !has_pred1 negb_or p'ennx0 andbT.
by apply: contraFN ex0Fnx0 => /mem_belast/(path_connect nx0Fp); rewrite cfaceC.
Qed.

Lemma sub_cface_icpA : subrel (cface : rel G) (cface : rel ecpA).
Proof.
apply: connect_sub => x _ /eqP<-; rewrite (@cface1 ecpA) /= {2}/ecpA_face.
have:= ecpA_merge; rewrite cfaceC edgeK => nx0Ffex0.
by case: ifP => // _; do 2!case: eqP => [-> //|_]; rewrite (@cfaceC ecpA).
Qed.

Lemma cface_icpA (x y : G) :
 (cface : rel ecpA) x y =
    cface x y || all (mem (fband [:: face (edge x0); node x0])) [:: x; y].
Proof.
set a := fband _.
have [_ eqFa']: fun_adjunction (id : ecpA -> G) face face [predC a].
  have clFa: fclosed face [predC a] by apply: predC_closed; apply: fbandF.
  apply: {x y} (strict_adjunction cfaceC) => // [|x y /negbNE/= a'x].
    by apply/subsetP => x _; apply: codom_f.
  apply/esym/baseF_ecpA; rewrite /icpA; apply: contra a'x => /pred2P[] -> /=.
    by rewrite unfold_in /= fconnect1.
  by rewrite unfold_in /= orbCA cface1 nodeK connect0.
rewrite orbC /=; have [| /eqFa'-> //] := boolP (x \in a).
have [| a'y] := boolP (y \in a); last by rewrite cfaceC (@cfaceC ecpA) eqFa'.
rewrite !unfold_in => /hasP[t Dt yFt] /hasP[z Dz xFz] /=.
apply: {x xFz}(connect_trans (sub_cface_icpA xFz)).
rewrite cfaceC {y yFt}(same_cface (sub_cface_icpA yFt)).
move: ecpA_merge Dz Dt; rewrite edgeK !inE => fex0Fnx0.
by case/pred2P=> -> /pred2P[]-> //; rewrite cfaceC.
Qed.

Lemma sub_adj_icpA : subrel (adj : rel G) (adj : rel ecpA).
Proof.
move=> x y; case/adjP=> z xFz zRy; apply/adjP.
exists z; apply: sub_cface_icpA; rewrite {x xFz}//= /ecpA_edge if_neg.
case: ifP => // ex0Fnx0; do 2?case: eqP => [Dz | _] //.
  by rewrite cface1 nodeK -(same_cface ex0Fnx0) -Dz.
by rewrite (same_cface ex0Fnx0) -(canLR nodeK Dz) -cface1.
Qed.

(* The two basic extension constructions. Since they both add an edge pair, *)
(* they share the common underlying dart set construction. We use a special *)
(* purpose concrete type, rather than the general set sum, so that case     *)
(* analysis will be better behaved.                                         *)

Section EcpDart.

Variable A : Type.

Inductive ecp_dart : predArgType := IcpX | IcpXe | Icp of A.

Lemma ecp_inj : injective Icp. Proof. by move=> x y [Dx]. Qed.
Definition ecp_encode u :=
  match u with IcpX => None | IcpXe => Some None | Icp x => Some (Some x) end.
Definition ecp_decode u :=
  match u with None => IcpX | Some None => IcpXe | Some (Some x) => Icp x end.
Fact ecp_cancel : cancel ecp_encode ecp_decode. Proof. by case. Qed.

End EcpDart.

(* Coq divergence bug!!!
  In principle we should be able to use these generic constructions to get
  an eqType structure for ecp_dart. In practice the nested matches (4 levels!)
  cause the Coq kernel to diverge badly, e.g., on the Qed of cface_ecpH below.
Definition ecp_eqMixin (A : eqType) := CanEqMixin (@ecp_cancel a).
Canonical ecp_eqType (A : eqType) := EqType (ecp_dart A) (ecp_eqMixin A).
*)

Section EcpEq.

Variable A : eqType.

Definition ecp_eq u v := match u, v with
 | IcpX, IcpX | IcpXe, IcpXe => true
 | Icp x, Icp y => x == y :> A
 | _, _ => false
 end.

Lemma ecp_eqP : Equality.axiom ecp_eq.
Proof. case=> [||x] [||y]; by [constructor | apply: (iffP eqP) => [->|[]]]. Qed.

Canonical ecp_eqMixin := EqMixin ecp_eqP.
Canonical ecp_eqType := EqType (ecp_dart A) ecp_eqMixin.

End EcpEq.

Definition ecp_choiceMixin (A : choiceType) := CanChoiceMixin (@ecp_cancel A).
Canonical ecp_choiceType (A : choiceType) :=
  ChoiceType (ecp_dart A) (ecp_choiceMixin A).
Definition ecp_countMixin (A : countType) := CanCountMixin (@ecp_cancel A).
Canonical ecp_countType (A : countType) :=
  CountType (ecp_dart A) (ecp_countMixin A).
Definition ecp_finMixin (A : finType) := CanFinMixin (@ecp_cancel A).
Canonical ecp_finType (A : finType) := FinType (ecp_dart A) (ecp_finMixin A).

Lemma card_ecp (A : finType) : #|ecp_dart A| = #|A|.+2.
Proof.
rewrite -(card_image (can_inj (@ecp_cancel _))) -!card_option.
by apply: eq_card => u; apply/imageP; exists (ecp_decode u); case: u => [[]|].
Qed.

Definition ecp_edge x :=
  match x with
  | IcpX => IcpXe G
  | IcpXe => IcpX G
  | Icp x' => Icp (edge x')
  end.

Definition ecpU_node x :=
  match x with
  | IcpX => IcpXe G
  | IcpXe => Icp (node (node x0))
  | Icp y => if y == node x0 then IcpX G else Icp (node y)
  end.

Definition ecpU_face x :=
  match x with
  | IcpX => IcpX G
  | IcpXe => Icp (node x0)
  | Icp y => if face y == node x0 then IcpXe G else Icp (face y)
  end.

Fact ecpU_subproof : cancel3 ecp_edge ecpU_node ecpU_face.
Proof.
move=> [||x] //=; first by rewrite eqxx.
by case: ifP => /= [/eqP <- | ->]; rewrite edgeK.
Qed.

Definition ecpU_map := Hypermap ecpU_subproof.

Definition ecpU := PointedMap ecpU_map (IcpX G).

Definition icpU : G -> ecpU := @Icp G.

Lemma icpU_inj : injective icpU. Proof. exact: ecp_inj. Qed.

Lemma icpU_edge : {morph icpU: x / edge x}. Proof. by []. Qed.

(* The N step is a K step applied immediately to the left of the ring head.   *)
(* We get the K step below by composition with R steps, and the H and Y steps *)
(* by composition with a U step.                                              *)

Definition ecpN_node x :=
  match x with
  | IcpX =>  if long_cpring x0 then Icp (node x0) else IcpX G
  | IcpXe => Icp (face (edge x0))
  | Icp y => if y == x0 then IcpXe G else
             if node (node y) == x0 then IcpX G else Icp (node y)
  end.

Definition ecpN_face x :=
  match x with
  | IcpX =>  Icp x0
  | IcpXe => if long_cpring x0 then Icp (face (edge (face (edge x0)))) else
             IcpX G
  | Icp y => if y == edge (face (edge x0)) then IcpXe G else
             if y == edge (node x0) then IcpX G else Icp (face y)
  end.

Lemma ecpN_subproof : cancel3 ecp_edge ecpN_node ecpN_face.
Proof.
move=> [||x]; rewrite /= ?eqxx //.
  case: ifP => x0gt2 /=; last by rewrite x0gt2.
  by rewrite -(inj_eq nodeI) !edgeK eqxx (negPf x0gt2).
rewrite !(inj_eq edgeI) -(canF_eq nodeK).
case: ifP => /= [/eqP <- | x0'nx]; first by rewrite nodeK.
case: ifP => /= [/eqP Dx | nx0'x].
  by rewrite if_neg -Dx eq_sym -(canF_eq nodeK) x0'nx.
by rewrite -(inj_eq nodeI) edgeK x0'nx nx0'x.
Qed.

Definition ecpN_map := Hypermap ecpN_subproof.

Definition ecpN := PointedMap ecpN_map (IcpX G).

Definition icpN : G -> ecpN := @Icp G.

Lemma icpN_inj : injective icpN. Proof. exact: ecp_inj. Qed.

Lemma icpN_edge : {morph icpN : x / edge x}. Proof. by []. Qed.

Lemma plain_ecpU : plain ecpU.
Proof.
apply/plainP=> [] [||x] // _; have [eex x'ex] := plainP plainG x isT.
by rewrite -!icpN_edge eex.
Qed.

Lemma plain_ecpN : plain ecpN.
Proof. exact: plain_ecpU. Qed.

Lemma baseN_ecpU : fun_base icpU node node (pred1 (Icp (node x0))).
Proof. by move=> x y; rewrite /= -if_neg => ->. Qed.

Lemma icpU_node : {in [predC [:: node x0]], {morph icpU : x / node x}}.
Proof. by move=> x; rewrite !inE /= => /negPf->. Qed.

Lemma cpring_ecpU :
  cpring ecpU = [:: node ecpU, ecpU : ecpU & map icpU (cpring x0)].
Proof.
apply: cpring_def => //; apply/andP; split.
move: (cpring_uniq x0) (cycle_rev_cpring x0); rewrite head_cpring /=.
  rewrite !rev_cons -map_rev -mem_rev -rev_uniq; move: (rev _) => p /andP[Up _].
  do 4 rewrite -rot1_cons rot_cycle -?rcons_cons; rewrite /= !eqxx -map_rcons.
  case: p Up => [|x p] Up //=; rewrite (map_path baseN_ecpU) //.
  by rewrite belast_rcons -has_map has_pred1 (mem_map icpU_inj).
rewrite rev_uniq /= !inE (map_inj_uniq icpU_inj) cpring_uniq andbT.
by do 2?case: mapP => [[] | _] //.
Qed.

Lemma size_cpring_ecpU : size (cpring ecpU) = (size (cpring x0)).+2.
Proof. by rewrite cpring_ecpU /= size_map. Qed.

Lemma cubic_ecpU : quasicubic (rev (cpring ecpU)).
Proof.
rewrite cpring_ecpU; apply/cubicP => u; rewrite inE /= mem_rev !inE.
case: u => [||x] //=; rewrite (mem_map icpU_inj) -mem_rev => x0N'x.
have [n3x x'nx] := cubicP cubicG x x0N'x; rewrite mem_rev mem_cpring in x0N'x.
case: eqP => [Dx | _]; first by rewrite Dx fconnect1 in x0N'x.
split; rewrite //= (inj_eq nodeI).
case: eqP => /= [Dx | x0'x]; first by rewrite Dx connect0 in x0N'x.
rewrite /= (inj_eq nodeI) n3x; case: eqP => // Dx.
by rewrite -Dx cnodeC fconnect1 in x0N'x.
Qed.

Lemma baseN_ecpN :
  fun_base icpN node node (pred2 (Icp x0) (Icp (face (edge (face (edge x0)))))).
Proof.
move=> x y; rewrite /= !(inj_eq icpN_inj) -!(canF_eq nodeK). 
by case/norP=> /negPf-> /negPf->.
Qed.

Lemma cpring_ecpN :
 cpring ecpN =
   if long_cpring x0 then
     [:: icpN (node x0), ecpN : ecpN & map icpN (drop 3 (cpring x0))]
   else [:: ecpN : ecpN].
Proof.
case: ifP => [x0gt2 | x0le1]; last first.
  by apply cpring_def; rewrite /ucycle /= /frel /ecpN_node x0le1.
apply cpring_def; [by rewrite /= x0gt2 | apply/andP; split].
  move: (cpring_uniq x0) (cycle_rev_cpring x0).
  rewrite (head_long_cpring x0gt2) /= drop0; move: (drop 3 _) => p.
  rewrite !rev_cons -map_rev !inE -!(mem_rev p) -rev_uniq !negb_or.
  move: {p}(rev p) => p /and4P[/and3P[x0'nx0 _ p'nx0] /andP[_ p'x0] _ Up].
  do 5!rewrite -rot1_cons rot_cycle -?rcons_cons.
  rewrite (cycle_path x0) (cycle_path (IcpX G)) /= last_map.
  case/and4P=> /eqP Lp _ _ nx0Np.
  rewrite (map_path baseN_ecpN) ?has_predU ?has_pred1 /ecpN_node ?x0gt2 /=.
    by rewrite -(inj_eq nodeI) Lp edgeK (negPf x0gt2) !eqxx.
  apply/orP; case => [/mem_belast|]; first by rewrite inE eq_sym=> /norP[]. 
  have: uniq (node x0 :: p) by rewrite /= p'nx0.
  by rewrite -Lp nodeK lastI rcons_uniq => /andP[/negP].
have:= cpring_uniq x0; rewrite (head_long_cpring x0gt2) rev_uniq /= drop0.
move: (drop 3 _) => p; rewrite !inE (map_inj_uniq icpN_inj) (mem_map icpN_inj).
by rewrite orbA => /and4P[/norP[_ ->] _ _ ->]; case: mapP => [[]|].
Qed.

Lemma rot1_cpring_ecpN :
  rot 1 (cpring ecpN) = (ecpN : ecpN) :: map icpN (drop 2 (rot 1 (cpring x0))).
Proof.
rewrite cpring_ecpN; case: ifP => [x0gt2|].
  by rewrite (head_long_cpring x0gt2) /= !drop0 map_cat.
by rewrite size_long_cpring; case: (cpring x0) => [|x [|y [|z p]]].
Qed.

Lemma size_cpring_ecpN : size (cpring ecpN) = (size (cpring x0)).-2.+1.
Proof.
rewrite -(size_rot 1) rot1_cpring_ecpN drop_behead.
by rewrite /= size_map !size_behead size_rot.
Qed.

Lemma cubic_ecpN : quasicubic (rev (cpring ecpN)).
Proof.
pose qXe := [:: edge ecpN; icpN (face (edge x0)); icpN x0].
have cubic_qXe: cubicb (mem qXe).
  have cycNqXe: fcycle node qXe.
    by rewrite /= !eqxx -(inj_eq nodeI) edgeK -(eq_sym x0) (negPf x0gt1) eqxx.
  apply/subsetP=> u qXe_u; rewrite inE (order_cycle cycNqXe) //= andbT.
  by rewrite inE (inj_eq icpN_inj) (canF_eq (canF_sym nodeK)).
apply/cubicP=> u; rewrite inE /= mem_rev -(mem_rot 1) rot1_cpring_ecpN.
case qXe_u: (u \in qXe); first by clear 1; apply: (cubicP cubic_qXe).
case: u qXe_u => [||x] //=.
rewrite !inE (mem_map icpN_inj) !(inj_eq icpN_inj) !orFb.
move/norP=> [fex0'x x0'x] p'x; rewrite (negPf x0'x).
have{p'x} x0N'x: x \notin rev (cpring x0).
  case x0gt2: (long_cpring x0).
    move: p'x; rewrite (head_long_cpring x0gt2) rot1_cons /= drop0 mem_rcons.
    by rewrite mem_rev /= !inE !negb_or x0'x fex0'x.
  rewrite {p'x} mem_rev mem_cpring fconnect_orbit /orbit.
  have:= x0gt2; rewrite size_long_cpring size_cpring -orderSpred /= inE.
  rewrite (negPf x0'x); case: _.-1 => [|[|n]] //= _; rewrite inE.
  by move/eqP: x0gt2 => <-.
have [n3x x'nx] := cubicP cubicG _ x0N'x; rewrite mem_rev mem_cpring in x0N'x.
case: ifP => [/eqP nnx | x0'nnx].
  by rewrite -nnx -2!cnode1 connect0 in x0N'x.
split=> //=; rewrite n3x (negPf x0'x) (canF_eq nodeK) (negPf fex0'x).
by rewrite /= x0'nnx n3x (canF_eq nodeK) (negPf fex0'x).
Qed.

Lemma connected_ecpU : connected ecpU.
Proof.
apply/eqP/esym; rewrite -(n_comp_connect (@glinkC ecpU) ecpU).
have GXe: gcomp ecpU (edge ecpU) by apply: connect1; apply: glinkE.
have Gnnx0: gcomp ecpU (icpU (node (node x0))).
  by rewrite 2!(same_connect1 glinkC (glinkN _)) /=.
apply: eq_n_comp_r => [[||x]]; rewrite !inE ?connect0 //.
have [p] := connected_clink x (node (node x0)) ccG.
elim: p x => [|y p IHp] x /= => [_ <- // | /andP[xCy yCp] /(IHp _ yCp) Gy].
have{p IHp yCp xCy} [xny | fxy] := clinkP xCy.
  rewrite (same_connect1r glinkC (glinkN _)) /= -xny in Gy.
  by case: eqP Gy => // ynx0 _; rewrite xny ynx0.
by rewrite (same_connect1r (@glinkC ecpU) (glinkF _)) /= fxy; case: ifP.
Qed.

Lemma connected_ecpN : connected ecpN.
Proof.
apply/eqP/esym; rewrite -(n_comp_connect (@glinkC ecpN) ecpN).
have GXe: gcomp ecpN (edge ecpN) by rewrite connect1 ?glinkE.
have Gx0: gcomp ecpN (icpN x0) by rewrite connect1 ?glinkF.
have Gfex0: gcomp ecpN (icpN (face (edge x0))).
  by rewrite (same_connect1r glinkC (glinkN _)) in GXe.
have Gnx0: gcomp ecpN (icpN (node x0)).
  case x0gt2: (long_cpring x0); last by move/eqP: x0gt2 => <-.
  by rewrite (same_connect1 glinkC (glinkN _)) /= x0gt2.
apply: eq_n_comp_r => [[||x]]; rewrite !inE ?connect0 //.
have [p] := connected_clink x x0 ccG.
elim: p x => [|y p IHp] x /= => [_ <- // | /andP[xCy yCp] /(IHp y yCp) Gy].
have{p IHp yCp xCy} [xny | fxy] := clinkP xCy.
  rewrite (same_connect1r glinkC (glinkN _)) /= -xny in Gy.
  case: eqP Gy => [yx0 | _]; first by rewrite xny yx0.
  by case: eqP => // /(canRL nodeK)->.
rewrite (same_connect1r (@glinkC ecpN) (glinkF _)) /= fxy.
by do 2!case: ifP => // _; apply: connect0.
Qed.

Lemma cface_ecpU : cface ecpU =1 xpred1 (ecpU : ecpU).
Proof. by move=> u; rewrite /= -mem_seq1; apply: fconnect_cycle. Qed.

Lemma closedF_ecpU : fclosed face (predC1 (ecpU : ecpU)).
Proof. by move=> u _ /=/eqP <-; rewrite !inE -!cface_ecpU -cface1r. Qed.

Lemma adjnF_ecpU : fun_adjunction icpU face face (predC1 (ecpU : ecpU)).
Proof.
pose h u (_ : predC1 (ecpU : ecpU) u) := if u is Icp x then x else node x0.
apply: (intro_adjunction cfaceC closedF_ecpU h) => [|x /= _]; last first.
  split=> // _ /eqP <-; rewrite (@cface1 ecpU) /=.
  by case: eqP => // ->; apply: fconnect1.
case=> [||x] //= _.
  by split; [apply: fconnect1 | case=> //= y _ /(_ =P y) <-].
split=> // [] [||y] //= _; case: (face x =P _) => //.
  by move=> <- _; apply: fconnect1.
by move=> _ /(_ =P y) <-; apply: fconnect1.
Qed.

Lemma cface_icpU : {mono icpU : x y / cface x y}.
Proof. by move=> x y; have [_ ->] := adjnF_ecpU. Qed.

Lemma adj_ecpU u : adj ecpU u = (u \in fband [:: icpU (node x0)]).
Proof.
rewrite /adj /orbit /order (eq_card cface_ecpU) (card1 ecpU) /=.
by rewrite /rlink cface1 cfaceC.
Qed.

Lemma adj_icpU : {mono icpU : x y / adj x y}.
Proof.
move=> x y; apply/adjP/adjP => [[[||z] xFz zRy] | [z xFz zRy]].
- by rewrite cfaceC cface_ecpU in xFz.
- by rewrite /rlink /= cface_ecpU in zRy.
- by exists z; rewrite /rlink -cface_icpU.
by rewrite /rlink -!cface_icpU in xFz zRy; exists (icpU z).
Qed.

Lemma fband_icpU u : {x : G | cface u (icpU x)} + {cface ecpU u}.
Proof.
rewrite cface_ecpU; case: eqP; first by right.
by case: u => // [|x] _; left; [exists (node x0); apply: fconnect1 | exists x].
Qed.

Lemma bridgeless_ecpU : bridgeless ecpU.
Proof.
have X'eX: ~ cface ecpU (edge ecpU) by rewrite cface_ecpU.
apply/existsP=> [] [[||x]] //; first by rewrite cfaceC.
by rewrite cface_icpU bridgeless_cface.
Qed.

Lemma planar_ecpU : planar ecpU.
Proof.
have oFX: fcard face ecpU = (fcard face G).+1.
  rewrite (n_compC (pred1 (ecpU : ecpU))) -add1n; congr (_ + _).
    by rewrite -(eq_n_comp_r cface_ecpU) (n_comp_connect cfaceC).
  by rewrite (adjunction_n_comp _ cfaceC cfaceC closedF_ecpU adjnF_ecpU).
have geoX: ucycle_plain_quasicubic_connected (rev (cpring ecpU)).
  split; [split; last exact: ucycle_rev_cpring | exact connected_ecpU].
  by split; [apply plain_ecpU | apply cubic_ecpU].
rewrite (quasicubic_Euler geoX) card_ecp oFX /nilp size_rev.
rewrite size_cpring_ecpU add1n !doubleS !addSn 4!addnS mulnS !eqSS.
by have:= planarG; rewrite (quasicubic_Euler geoG) /nilp size_rev head_cpring.
Qed.

Lemma cface_ecpN : cface ecpN (icpN x0).
Proof. exact: fconnect1. Qed.

Lemma adjnF_ecpN : fun_adjunction icpN face face ecpN.
Proof.
pose h := match _ with Icp x => x | IcpX => x0 | _ => edge (face (edge x0)) end.
apply: (intro_adjunction cfaceC _ (fun u _ => h u)) => //= [|x _]; last first.
  split=> // _ /eqP <-; rewrite (@cface1 ecpN) /=; case: eqP => [-> | _].
    rewrite (@cface1 ecpN) /=; case: ifP => // /eqP->.
    by rewrite nodeK fconnect1.
  by case: eqP => // ->; rewrite nodeK fconnect1.
case=> [||x] /= _.
- by split=> [|_ _ /eqP<- //]; rewrite fconnect1.
- split=> [|_ _ /eqP<-]; first by rewrite (@cface1r ecpN) /= eqxx.
  by case: ifP => [_ | /eqP->]; rewrite cface1 ?nodeK.
by split=> // _ _ /eqP <-; do 2?case: eqP => [-> | ] //=; rewrite cface1 ?nodeK.
Qed.

Lemma cface_icpN : {mono icpN : x y / cface x y}.
Proof. by move=> x y; have [_ ->] :=  adjnF_ecpN. Qed.

Lemma adj_icpN : 
  let adjx0 x y := cface (edge (face (edge x0))) x && cface x0 y in
  forall x y, adj (icpN x) (icpN y) = [|| adj x y, adjx0 x y | adjx0 y x].
Proof.
move=> /= x y; apply/adjP/idP=> [[[||z] xFz zRy]|].
- rewrite cface1r /= cface_icpN cfaceC in xFz.
  by rewrite xFz orbA orbC -cface_icpN cface1 /= eqxx [fconnect _ _ _]zRy.
- rewrite [rlink _ _]cface1 cface_icpN in zRy.
  by rewrite zRy -cface_icpN cface1 cfaceC /= eqxx xFz orbT.
- by case: adjP => // [[]]; exists z; rewrite /rlink -cface_icpN.
case/or3P=> [/adjP[z xFz zRy] | /andP[zFx zFy] | /andP[zFy zFx]].
- by exists (icpN z); rewrite /rlink cface_icpN.
- exists (edge ecpN); last by rewrite /rlink cface1 cface_icpN.
  by rewrite cfaceC -cface_icpN cface1r /= eqxx in zFx.
exists (ecpN : ecpN); first by rewrite cfaceC cface1 cface_icpN.
by rewrite -cface_icpN cface1 /= eqxx in zFy.
Qed.

Lemma sub_adj_icpN : {homo icpN: x y / adj x y}.
Proof. by move=> x y xAy; rewrite /= adj_icpN xAy. Qed.

Lemma fband_icpN u : {x : G | cface u (icpN x)}.
Proof.
case: u => [||x].
- by exists x0; rewrite cface1 /= cface_icpN.
- by exists (edge (face (edge x0))); rewrite cface1r /= eqxx.
by exists x; rewrite cface_icpN.
Qed.

Lemma planar_ecpN : planar ecpN.
Proof.
have oFX: fcard face ecpN = fcard face G.
  exact: (adjunction_n_comp _ cfaceC cfaceC _ adjnF_ecpN).
have geoX: ucycle_plain_quasicubic_connected (rev (cpring ecpN)).
  split; [split; last exact: ucycle_rev_cpring | exact connected_ecpN ].
  by split; [ apply plain_ecpN | apply cubic_ecpN ].
rewrite (quasicubic_Euler geoX) oFX card_ecp /nilp size_rev size_cpring_ecpN.
have:= planarG; rewrite (quasicubic_Euler geoG) size_rev head_proper_cpring //=.
by rewrite /nilp size_rev !add1n !doubleS !addnS.
Qed.

End ExtConfig.

Lemma ecpR1_eq (G : hypermap) x0 : ecpR 1 x0 = face (edge x0) :> G.
Proof. by rewrite /= subn1 -{3}(f_finv nodeI x0) nodeK. Qed.

Section CompExtConfig.

Variables (n0 : nat) (G : hypermap) (x0 : G).

Hypotheses (planarG : planar G) (bridge'G : bridgeless G).
Hypotheses (plainG : plain G) (cubicG : quasicubic (rev (cpring x0))).
Hypotheses (ccG : connected G) (x0gt1 : proper_cpring x0).
Hypothesis Urg : simple (cpring x0).

Definition ecpR' := ecpR (order node x0).-1 x0.

Definition icpR' : G -> ecpR' := icpR _ _.

Lemma ecpR'_eq : ecpR' = node x0 :> G.
Proof. by rewrite /ecpR' /ecpR /= -orderSpred /= subSnn. Qed.

Definition ecpK := ecpR 1 (ecpN ecpR').

Definition icpK x : ecpK := icpR 1 (ecpN ecpR') (icpN ecpR' (icpR' x)).

Lemma size_cpring_ecpK : size (cpring ecpK) = (size (cpring x0)).-2.+1.
Proof.
by rewrite /ecpK size_cpring_ecpR size_cpring_ecpN /ecpR' size_cpring_ecpR /=.
Qed.

Lemma icpK_inj : injective icpK. Proof. by move=> x y []. Qed.

Lemma icpK_edge : {morph icpK : x / edge x}. Proof. by []. Qed.

Lemma cpring_ecpK : cpring ecpK = node ecpK :: map icpK (drop 2 (cpring x0)).
Proof.
rewrite cpring_ecpR rot1_cpring_ecpN ecpR1_eq edgeK cpring_ecpR -subn1.
by rewrite -size_cpring rotrK.
Qed.

Lemma cface_icpK : {mono icpK : x y / cface x y}.
Proof. exact: (cface_icpN ecpR'). Qed.

Lemma adj_icpK :
  let adjx0 x y := cface (edge x0) x && cface (node x0) y in
  forall x y, adj (icpK x) (icpK y) = [|| adj x y, adjx0 x y | adjx0 y x].
Proof.
by move=> /= x y; apply: (etrans (adj_icpN ecpR' _ _)); rewrite ecpR'_eq nodeK.
Qed.

Lemma sub_adj_icpK : {homo icpK : x y / adj x y}.
Proof. by move=> x y xAy; rewrite /= adj_icpK xAy. Qed.

Lemma cface_node_ecpK : cface (node ecpK) (icpK (node x0)).
Proof. rewrite /ecpK ecpR1_eq edgeK ecpR'_eq; apply: cface_ecpN. Qed.

Lemma cface_ecpK : cface ecpK (icpK (face (edge x0))).
Proof.
rewrite /ecpK ecpR1_eq ecpR'_eq /= nodeK; case: ifP => // /eqP.
by rewrite (@cface1 (ecpN _)) nodeK /= => {3}->; rewrite nodeK.
Qed.

Lemma fband_icpK u : {x : G | cface u (icpK x)}.
Proof. exact: fband_icpN. Qed.

Definition ecpY := ecpN (ecpU x0).

Lemma plain_ecpY : plain ecpY.
Proof. by do 2!apply: plain_ecpN. Qed.

Lemma cubic_ecpY : quasicubic (rev (cpring ecpY)).
Proof. by apply: cubic_ecpN => //; apply: cubic_ecpU. Qed.

Lemma size_cpring_ecpY : size (cpring ecpY) = (size (cpring x0)).+1.
Proof. by rewrite size_cpring_ecpN size_cpring_ecpU. Qed.

Lemma planar_ecpY : planar ecpY.
Proof.
apply: planar_ecpN => //.
- exact: planar_ecpU.
- exact: plain_ecpU.
- exact: cubic_ecpU.
exact: connected_ecpU.
Qed.

Lemma connected_ecpY : connected ecpY.
Proof. by apply: connected_ecpN; apply: connected_ecpU. Qed.

Definition icpY x : ecpY := icpN _ (icpU x0 x).

Lemma icpY_inj : injective icpY. Proof. by move=> x y []. Qed.

Lemma icpY_edge : {morph icpY : x / edge x}. Proof. by []. Qed.

Lemma icpY_node : {in [predC [:: node x0; x0]], {morph icpY : x / node x}}.
Proof.
move=> x; rewrite !inE => /norP[nx0'x x0'x] /=.
by rewrite (negPf nx0'x) /= (inj_eq nodeI) (negPf x0'x).
Qed.

Lemma drop2_cpring_ecpY : drop 2 (cpring ecpY) = map icpY (behead (cpring x0)).
Proof. by rewrite cpring_ecpN cpring_ecpU head_cpring /= !drop0 -map_comp. Qed.

Lemma cpring_ecpY :
  cpring ecpY = [:: node ecpY, ecpY : ecpY & map icpY (behead (cpring x0))].
Proof. by rewrite -drop2_cpring_ecpY -head_proper_cpring. Qed.

Lemma cface_icpY : {mono icpY : x y / cface x y}.
Proof. by move=> x y; rewrite /icpY cface_icpN cface_icpU. Qed.

Lemma adj_icpY : {mono icpY : x y / adj x y}.
Proof.
by move=> x y; rewrite /icpY adj_icpN adj_icpU !cface_ecpU /= !andbF !orbF.
Qed.

Lemma cface_node_ecpY : cface (node ecpY) (icpY (node x0)).
Proof. by rewrite cface1 cface_icpY connect0. Qed.

Lemma cface_ecpY u : cface ecpY u = (u \in [:: ecpY : ecpY; face ecpY]).
Proof. exact: fconnect_cycle. Qed.

Lemma adj_ecpY u : adj ecpY u = (u \in fband (map icpY [:: node x0; x0])).
Proof.
apply/adjP/hasP => [[v] | [v Dv uFv]].
  rewrite cface_ecpY !inE /rlink cface1 cfaceC => /pred2P[] ->{v} XRu.
    exists (icpY x0); first by rewrite map_f // !inE eqxx orbT.
    by rewrite /= nodeK (negPf x0gt1) in XRu.
  by exists (icpY (node x0)); rewrite ?map_f // mem_head.
exists (node v); last by rewrite /rlink cface1 nodeK cfaceC.
move: Dv; rewrite cface_ecpY !inE => /pred2P[] -> /=; rewrite ?eqxx ?orbT //.
by rewrite (negPf x0gt1) /= !eqxx.
Qed.

Lemma fband_icpY u : {x | cface u (icpY x)} + {cface ecpY u}.
Proof.
have [v uFv] := fband_icpN u.
have [[x xFv] | XFv] := fband_icpU v; [left | right].
  by exists x; rewrite (same_cface uFv) cface_icpN.
by rewrite (same_connect_r cfaceC uFv) cface1 cface_icpN.
Qed.

Lemma bridgeless_ecpY : bridgeless ecpY.
Proof.
have /idP X'eX := cface_ecpY (edge ecpY).
have /idP fX'efX := cface_ecpY (edge (face ecpY)); rewrite cface1 in fX'efX.
apply/existsP=> [] [] [||[||x]] //; try by rewrite cfaceC.
by rewrite cface_icpY bridgeless_cface.
Qed.

Definition ecpH := ecpN ecpY.

Lemma plain_ecpH : plain ecpH.
Proof. by apply: plain_ecpN; apply plain_ecpY. Qed.

Lemma cubic_ecpH : quasicubic (rev (cpring ecpH)).
Proof. by apply: cubic_ecpN => //; apply cubic_ecpY. Qed.

Lemma size_cpring_ecpH : size (cpring ecpH) = size (cpring x0).
Proof. by rewrite /ecpH size_cpring_ecpN size_cpring_ecpY head_cpring. Qed.

Lemma planar_ecpH : planar ecpH.
Proof.
apply: planar_ecpN => //.
- exact planar_ecpY.
- exact plain_ecpY.
- exact cubic_ecpY.
exact connected_ecpY.
Qed.

Lemma connected_ecpH : connected ecpH.
Proof. by apply: connected_ecpN; apply connected_ecpY. Qed.

Definition icpH x : ecpH := icpN _ (icpY x).

Lemma icpH_inj : injective icpH. Proof. by move=> x y []. Qed.

Lemma icpH_edge : {morph icpH : x / edge x}. Proof. by []. Qed.

Lemma icpH_node :
  {in [predC [:: node x0; x0; face (edge x0)]], {morph icpH : x / node x}}.
Proof.
move=> x; rewrite !inE !negb_or => /and3P[nx0'x x0'x fex0'x].
rewrite /= (negPf nx0'x) /=; do !rewrite (inj_eq nodeI, negPf x0'x) /=.
by rewrite (canF_eq nodeK) (negPf fex0'x).
Qed.

Lemma cface_icpH : {mono icpH : x y / cface x y}.
Proof. by move=> x y; rewrite /icpH cface_icpN cface_icpY. Qed.

Lemma adj_icpH : {mono icpH : x y / adj x y}.
Proof.
by move=> x y; rewrite /icpH adj_icpN adj_icpY !cface_ecpY !andbF !orbF.
Qed.

Lemma drop2_cpring_ecpH : drop 2 (cpring ecpH) = map icpH (drop 2 (cpring x0)).
Proof.
rewrite cpring_ecpN size_long_cpring size_cpring_ecpY.
rewrite (drop_behead 3) iterS -drop_behead drop2_cpring_ecpY.
by case: (cpring x0) => [|y1 [|y2 [|y3 r]]] //=; rewrite -map_comp.
Qed.

Lemma cpring_ecpH :
  cpring ecpH = [:: node ecpH, ecpH : ecpH & map icpH (drop 2 (cpring x0))].
Proof.
rewrite -drop2_cpring_ecpH -head_proper_cpring //.
by rewrite size_proper_cpring size_cpring_ecpH -size_proper_cpring.
Qed.

Lemma cface_node_ecpH : cface (node ecpH) (icpH (node x0)).
Proof. by rewrite cface1 /= if_neg /=; do 2!rewrite nodeK (negPf x0gt1) /=. Qed.

Lemma cface_ecpH u :
  cface ecpH u = (u \in [:: ecpH : ecpH; face ecpH; face (face ecpH)]).
Proof. by apply: fconnect_cycle; rewrite //= nodeK (negPf x0gt1). Qed.

Lemma adj_ecpH u :
  adj ecpH u = (u \in fband (map icpH [:: node x0; x0; face (edge x0)])).
Proof.
rewrite adjF1 -[_ _ u]/(adj (icpN ecpY ecpY) u).
have [v uFv] := fband_icpN u; rewrite (adjFr uFv) adj_icpN connect0 andbT.
rewrite cfaceC !cface_ecpY (closed_connect (fbandF _) uFv) {u uFv}adj_ecpY.
have <-: icpY x0 = face (edge ecpY) by rewrite /= nodeK (negPf x0gt1).
rewrite !inE !unfold_in /= !orbF !(cface_icpN ecpY) orbA; congr (_ || _).
by rewrite cfaceC; apply: (@same_cface ecpY); rewrite cface_icpY fconnect1.
Qed.

Lemma fband_icpH u : {x | cface u (icpH x)} + {cface ecpH u}.
Proof.
have [v uFv] := fband_icpN u; have [[x vFx] | XFv] := fband_icpY v.
  by left; exists x; rewrite (same_cface uFv) cface_icpN.
by right; rewrite cface1 (same_connect_r cfaceC uFv) cface_icpN.
Qed.

Lemma bridgeless_ecpH : bridgeless ecpH.
Proof.
have /idP X'eX := cface_ecpH (edge ecpH).
have /idP := cface_ecpH (edge (face ecpH)); rewrite cface1 => fX'efX.
have /idP := cface_ecpH (edge (face (face ecpH))); rewrite 2!cface1 => ffX'effX.
apply/existsP => [] [] [||[||[||x]]] //; try by rewrite cfaceC.
by rewrite cface_icpH bridgeless_cface.
Qed.

End CompExtConfig.

Fact cpmap0_subproof : cancel3 negb negb id. Proof. by case. Qed.
Definition cpmap0 := Hypermap cpmap0_subproof.
Lemma cpring0 b : @cpring cpmap0 b = [:: ~~ b; b].
Proof. by case: b; apply: cpring_def. Qed.

Fixpoint cpmap (cp : cprog) : pointed_map :=
  match cp with
  | CpR n :: cp' => ecpR n (cpmap cp')
  | CpR' :: cp' => ecpR' (cpmap cp')
  | CpY :: cp' => ecpY (cpmap cp')
  | CpH :: cp' => ecpH (cpmap cp')
  | CpU :: cp' => ecpU (cpmap cp')
  | CpK :: cp' => ecpK (cpmap cp')
  | CpA :: cp' => ecpA (cpmap cp')
  | [::] => PointedMap cpmap0 true
  end.

Definition cfmap cf := cpmap (cfprog cf).
Definition cfring cf := rev (cpring (cfmap cf)).

Lemma cpmap_proper cp : cubic_prog cp -> proper_cpring (cpmap cp).
Proof.
rewrite size_proper_cpring.
elim: cp => [|s cp IHcp] /=; first by rewrite cpring0.
case: s => // [n|||] /IHcp x0gt1.
- by rewrite size_cpring_ecpR.
- by rewrite size_cpring_ecpY ltnW.
- by rewrite size_cpring_ecpH.
by rewrite size_cpring_ecpU.
Qed.

Lemma cfmap_long cp : config_prog cp -> long_cpring (cpmap cp).
Proof.
rewrite size_long_cpring; elim: cp => [|s cp IHcp] //=.
case: s => // [n||]; rewrite ?size_cpring_ecpR ?size_cpring_ecpH //.
rewrite size_cpring_ecpY.
by case: cp => [|s cp] in IHcp * => [_ | /IHcp/leqW//]; rewrite cpring0.
Qed.

Lemma cpmap_plain cp : cubic_prog cp -> plain (cpmap cp).
Proof.
elim: cp => [_ | s cp IHcp]; first by apply/plainP=> [] [].
case: s => // /IHcp plainG.
- exact: plain_ecpY.
- exact: plain_ecpH.
exact: plain_ecpU.
Qed.

Lemma cpmap_cubic cp : cubic_prog cp -> quasicubic (rev (cpring (cpmap cp))).
Proof.
elim: cp => [_ | s cp IHcp]; first by rewrite cpring0; apply/cubicP=> [] [].
case: s => // [n|||] /IHcp cubicG.
- exact: cubic_ecpR.
- exact: cubic_ecpY.
- exact: cubic_ecpH.
exact: cubic_ecpU.
Qed.

Lemma cpmap_connected cp : cubic_prog cp -> connected (cpmap cp).
Proof.
elim: cp => [_ | s cp IHcp].
  apply/eqP/esym; rewrite -(n_comp_connect (@glinkC cpmap0) true).
  by apply: eq_n_comp_r => [] []; rewrite ?inE connect1. 
case: s => // /IHcp ccG.
- exact: connected_ecpY.
- exact: connected_ecpH.
exact: connected_ecpU.
Qed.

Lemma cpmap_bridgeless cp : cubic_prog cp -> bridgeless (cpmap cp).
Proof.
elim: cp => [_ | s cp IHcp].
  by apply/existsP=> [] [b]; rewrite (@fconnect_cycle _ _ [::b]); case: b.
case: s => // cp_ok; have bridge'G := IHcp cp_ok.
- exact: bridgeless_ecpY.
- by apply: bridgeless_ecpH => //; apply: cpmap_proper.
exact: bridgeless_ecpU.
Qed.

Lemma cpmap_planar cp : cubic_prog cp -> planar (cpmap cp).
Proof.
elim: cp => [_|s cp IHcp].
  have geoG: ucycle_plain_quasicubic_connected (rev (@cpring cpmap0 true)).
    split; [split; last by rewrite cpring0 | exact: (@cpmap_connected [::])].
    by split; [ apply: (@cpmap_plain [::]) | apply: (@cpmap_cubic [::])].
  by rewrite (quasicubic_Euler geoG) cpring0 fcard_id card_bool.
case: s => //= cp_ok;
  have [plainG cubicG] := (cpmap_plain cp_ok, cpmap_cubic cp_ok);
  have [ccG planarG] := (cpmap_connected cp_ok, IHcp cp_ok).
- exact: planar_ecpY.
- exact: planar_ecpH.
exact: planar_ecpU.
Qed.

Fixpoint cpker (cp : cprog) : seq (cpmap cp) :=
  match cp with
  | CpR _ :: cp' => cpker cp'
  | CpY :: cp' => map (icpY (cpmap cp')) (cpker cp')
  | CpH :: cp' =>
      if cpring (cpmap cp') is [:: _, x & _] then
         map (icpH (cpmap cp')) (x :: cpker cp')
      else [::]
  | _ => [::]
  end.

Lemma cpmap_simple cp :
  config_prog cp -> simple (cpring (cpmap cp) ++ cpker cp).
Proof.
elim: cp => [|s cp IHcp] //=; case: s => // [n||] cp_ok.
- by rewrite cpring_ecpR /rot -catA simple_catCA catA cat_take_drop IHcp.
- rewrite cpring_ecpY cat_cons simple_cons.
  rewrite (closed_connect (fbandF _) (cface_node_ecpY _)).
  rewrite -simple_cons -cat1s catA -cat_rcons -cats1 -!catA simple_catCA.
  rewrite /= -map_cat -map_cons -cat_cons -head_cpring simple_cons.
  rewrite unfold_in (eq_has (@cface_ecpY _ _)) has_map has_pred0 /=.
  rewrite (simple_map (cface_icpY _)); case: cp IHcp cp_ok => // _ _.
  by rewrite cpring0 simple_cons unfold_in /= fconnect_id.
set G := cpmap cp; have properG := cpmap_proper (config_prog_cubic cp_ok).
rewrite cpring_ecpH // {2}head_proper_cpring // -/G cat_cons simple_cons.
rewrite (closed_connect (fbandF _) (cface_node_ecpH _)) // -simple_cons -cat1s.
rewrite catA -!cat_rcons -!cats1 -!catA simple_catCA 2!catA simple_catCA.
rewrite -catA simple_catCA -map_cat -!catA !cat1s -!map_cons -!cat_cons.
rewrite -head_proper_cpring // simple_cons (simple_map (cface_icpH G)).
by rewrite unfold_in (eq_has (cface_ecpH _)) // has_map has_pred0 IHcp.
Qed.

Lemma cpmap_cover cp :
  config_prog cp -> fband (cpring (cpmap cp) ++ cpker cp) =i cpmap cp.
Proof.
elim: cp => [|s cp IHcp] //=; case: s => // [n||] cp_ok u.
- by rewrite cpring_ecpR fband_cat fband_rot -fband_cat IHcp.
- rewrite cpring_ecpY !cat_cons !fband_cons orbCA; apply/orP.
  have [[x uFx] | XFu] := fband_icpY u; [ right | by left; rewrite cfaceC].
  rewrite (same_connect_r cfaceC (cface_node_ecpY _)) -fband_cons.
  rewrite -map_cat -map_cons -cat_cons -head_cpring unfold_in.
  rewrite {u uFx}(eq_has (same_cface uFx)) has_map (eq_has (cface_icpY _ x)).
  by case: cp IHcp cp_ok x => // _ _ []; rewrite cpring0 /= connect0 ?orbT.
have properG := cpmap_proper (config_prog_cubic cp_ok); set G := cpmap cp.
rewrite cpring_ecpH // {2}head_proper_cpring // !(fband_cat, fband_cons).
rewrite -!orbA orbCA (orbCA (u \in _)) -fband_cat -fband_cons.
rewrite (same_connect_r cfaceC (cface_node_ecpH _)) // -fband_cons.
rewrite -!cat_cons -!map_cons -head_proper_cpring // -map_cat; apply/orP.
have[[x uFx] | Xfu] := fband_icpH u; [right | by left; rewrite cfaceC].
rewrite unfold_in (eq_has (same_cface uFx)) has_map (eq_has (cface_icpH G x)).
exact: IHcp.
Qed.

Fixpoint injcp (cp1 cp2 : cprog) (x : cpmap cp2) : cpmap (catrev cp1 cp2) :=
  match cp1 with
  | [::] => x
  | s :: cp1' =>
    let x' := match s return cpmap (s :: cp2) with
    | CpY => icpY (cpmap cp2) x
    | CpH => icpH (cpmap cp2) x
    | CpU => icpU (cpmap cp2) x
    | CpK => icpK (cpmap cp2) x
    | _ => x
    end in injcp cp1' x'
  end.

Lemma injcp_inj cp1 cp2 : injective (@injcp cp1 cp2).
Proof.
elim: cp1 cp2 => [|s cp1 IHcp1] cp2 x y //; move/IHcp1{IHcp1}.
by case: s => //; do 3!move/(@ecp_inj _ _ _)=> //.
Qed.

Lemma sub_cface_injcp cp1 cp2 : {homo @injcp cp1 cp2 : x y / cface x y}.
Proof.
elim: cp1 cp2 => [|s cp1 IHcp] cp2 x y xFy //; case: s => *; apply: IHcp => //.
- by rewrite cface_icpY.
- by rewrite cface_icpH.
- by rewrite cface_icpU.
- by rewrite cface_icpK.
exact: sub_cface_icpA.
Qed.

Lemma sub_adj_injcp cp1 cp2 : {homo @injcp cp1 cp2 : x y / adj x y}.
Proof.
elim: cp1 cp2 => [|s cp1 IHcp] cp2 x y xAy //; case: s => *; apply: IHcp => //.
- by rewrite adj_icpY.
- by rewrite adj_icpH.
- by rewrite adj_icpU.
- exact: sub_adj_icpK.
exact: sub_adj_icpA.
Qed.

Lemma cface_injcp cp1 cp2 :
  cubic_prog cp1 -> {mono @injcp cp1 cp2 : x y / cface x y}.
Proof.
elim: cp1 cp2 => [|s cp1 IHcp] cp2 //=.
case: s => // [n|||] cp_ok x y; rewrite IHcp //.
- exact: cface_icpY.
- exact: cface_icpH.
exact: cface_icpU.
Qed.

Lemma edge_injcp cp1 cp2 :
  cubic_prog cp1 -> {morph @injcp cp1 cp2 : x / edge x}.
Proof.
by elim: cp1 cp2 => [|s cp1 IHcp] cp2 //; case: s => //= * x; rewrite -IHcp.
Qed.

Lemma adj_injcp cp1 cp2 :
  cubic_prog cp1 -> {mono @injcp cp1 cp2 : x y / adj x y}.
Proof.
elim: cp1 cp2 => [|s cp1 IHcp] cp2 //=.
case: s => // [n|||] cp_ok x y; rewrite IHcp //.
- exact: adj_icpY.
- exact: adj_icpH.
exact: adj_icpU.
Qed.

Lemma node_injcp cp1 cp2 :
    cubic_prog cp1 ->
  {in [predC cpring (cpmap cp2)], {morph @injcp cp1 cp2 : x / node x}}.
Proof.
elim: cp1 cp2 => [|[n||||||] cp1 IHcp] //= cp2 cp1ok x XN'x.
- by rewrite IHcp // 2!inE cpring_ecpR mem_rot.
- rewrite -IHcp -1?icpY_node //; first rewrite !inE mem_cpring in XN'x.
    by rewrite !inE; apply: contra XN'x => /pred2P[]->; rewrite -?cnode1r.
  rewrite 2!inE cpring_ecpY -/cpmap !inE (mem_map (@icpY_inj _ _)) !orFb.
  by apply: contra XN'x; apply: mem_behead.
- rewrite -IHcp -1?icpH_node //; first rewrite!inE mem_cpring in XN'x.
    rewrite !inE -/cpmap; apply: contra XN'x => /or3P.
    by case=> /eqP->; rewrite ?fconnect1 // cnode1r edgeK.
  rewrite cpring_ecpN cpring_ecpY -/cpmap; case: ifP => // _.
  rewrite !inE /= -map_drop -map_comp drop1 (mem_map (@icpH_inj _ _)).
  by apply: contra XN'x => /mem_behead/mem_behead.
rewrite -IHcp -1?icpU_node ?cpring_ecpU // -/cpmap.
  by apply: contra XN'x; rewrite head_cpring !inE => ->.
by rewrite !inE /= (mem_map (@icpU_inj _ _)).
Qed.

Lemma cnode_injcp cp1 cp2 :
    cubic_prog cp1 ->
  {in [predC cpring (cpmap cp2)], {mono @injcp cp1 cp2 : x y / cnode x y}}.
Proof.
move=> cp_ok x XN'x y; apply/idP/idP=> /iter_findex => [|<-].
  elim: {x}(findex _ _ _) {-2}x XN'x => [|n IHn] x XN'x.
    by move/injcp_inj->.
  rewrite iterSr -node_injcp // cnode1; apply: IHn.
  by rewrite !inE mem_cpring -cnode1r -mem_cpring.
elim: {x y}(findex _ _) {-3}x XN'x => // n IHn x XN'x.
rewrite iterSr cnode1 -node_injcp //; apply: IHn.
by rewrite !inE mem_cpring -cnode1r -mem_cpring.
Qed.

Fixpoint cprsize (cp : cprog) :=
  match cp with
  | [::] => 2
  | CpY :: cp' => (cprsize cp').+1
  | CpU :: cp' => (cprsize cp').+2
  | CpK :: cp' => (cprsize cp').-2.+1
  | CpA :: cp' => sub2ifgt2 (cprsize cp')
  | _ :: cp' => cprsize cp'
  end.

Lemma size_ring_cpmap cp : size (cpring (cpmap cp)) = cprsize cp.
Proof.
elim: cp => [|[n||||||] cp1]; rewrite ?cpring0 // /cprsize => <-.
- exact: size_cpring_ecpR.
- exact: size_cpring_ecpR.
- by rewrite size_cpring_ecpN size_cpring_ecpU.
- by rewrite !size_cpring_ecpN size_cpring_ecpU head_cpring.
- exact: size_cpring_ecpU.
- exact: size_cpring_ecpK.
exact: size_cpring_ecpA.
Qed.

Definition cpksize : cprog -> nat :=
  count (fun s => if s is CpH then true else false).

Lemma size_cpker cp : config_prog cp -> size (cpker cp) = cpksize cp.
Proof.
elim: cp => // [[] //=] cp IHcp cp_ok.
  by rewrite size_map; case: cp IHcp cp_ok.
rewrite (head_proper_cpring (cpmap_proper (config_prog_cubic _))) //=.
by rewrite size_map IHcp.
Qed.

Inductive cfmask := Cfmask of bitseq & bitseq.

Definition proper_cpmask cp cm :=
  let: Cfmask mr mk := cm in (size mr == cprsize cp) && (size mk == cpksize cp).

Definition cpmask cm cp :=
  let: Cfmask mr mk := cm in mask mr (cpring (cpmap cp)) ++ mask mk (cpker cp).

Definition cfmask1 cp i :=
  Cfmask (nseq (cprsize cp) false) (mkseq (pred1 i) (cpksize cp)).

Lemma proper_cpmask1 cp i : proper_cpmask cp (cfmask1 cp i).
Proof. by rewrite /= size_nseq size_mkseq !eqxx. Qed.

Lemma cpmask1 cp i :
    i < cpksize cp -> config_prog cp ->
  cpmask (cfmask1 cp i) cp = [:: nth (cpmap cp : cpmap cp) (cpker cp) i].
Proof.
move=> lt_i_cp cp_ok; move: (cpmap cp : cpmap cp) lt_i_cp => /= x0.
rewrite mask_false cat0s -size_cpker {cp_ok}// -{2}[i]addn0 /mkseq.
elim: (cpker cp) 0 i => // [x p IHp] j [|i] /= lt_i_cp.
  rewrite add0n eqxx -addn1; congr (_ :: _).
  elim: p 0 {x IHp lt_i_cp} => //= [x p IHp] i.
  by rewrite -addnS IHp -{2}[j]addn0 eqn_add2l.
by rewrite -{1}[j]add0n eqn_add2r /= addSnnS IHp.
Qed.

Fixpoint cpadj cm (cp : cprog) {struct cp} :=
  match cp, cm with
  | CpR n :: cp', Cfmask mr mk =>
      let: Cfmask mr' mk' := cpadj (Cfmask (rotr n mr) mk) cp' in
      Cfmask (rot n mr') mk'
  | CpY :: cp', Cfmask [:: b0, b1, b2 & mr] mk =>
    if cpadj (Cfmask [:: b0, b2 & mr] mk) cp' is Cfmask [:: a0, a2 & mr'] mk'
    then Cfmask [:: a0 || b1, b0 || b2, a2 || b1 & mr'] mk'
    else cm
  | CpH :: cp', Cfmask [:: b0, b1 & mr] (b1' :: mk) =>
    if cpadj (Cfmask [:: b0, b1' & mr] mk) cp' is Cfmask [:: a0, a1 & mr'] mk'
    then Cfmask [:: a0 || b1, [|| b0, b1' | head b0 mr]
                  & if mr' is a2 :: mr'' then (a2 || b1) :: mr'' else mr']
                ((a1 || b1) :: mk')
    else cm
  | [::], Cfmask [:: b0; b1] [::] => Cfmask [:: b1; b0] [::]
  | _, _ => cm (* can't happen *)
  end.

Lemma cpadj_proper cp cm :
  proper_cpmask cp cm -> proper_cpmask cp (cpadj cm cp).
Proof.
elim: cp cm => [|s cp IHcp] [mr mk].
  by case: mr mk => [|b0 [|b1 [|b2 mr]]] [].
case: s => //= [n||].
- move=> m_ok; set cm := Cfmask (rotr n mr) mk.
  have{m_ok} cm_ok: proper_cpmask cp cm by rewrite /= size_rotr.
  by case: (cpadj cm cp) (IHcp _ cm_ok) => mr' mk' /=; rewrite size_rot.
- case: mr => [|b0 [|b1 [|b2 mr]]] //= m_ok; set cm := Cfmask _ mk.
  by case: (cpadj cm cp) (IHcp cm m_ok) => [[|a0 [|a2 mr']] mk'].
case: mr mk => [|b0 [|b1 mr]] //= [|b1' mk] //= m_ok; set cm := Cfmask _ mk.
by case: (cpadj cm cp) (IHcp cm m_ok) => [[|a0 [|a1 [|a2 mr']]] mk'].
Qed.

Lemma cpmask_adj cp cm :
    config_prog cp -> proper_cpmask cp cm ->
 forall x, (x \in fband (cpmask (cpadj cm cp) cp)) = has (adj x) (cpmask cm cp).
Proof.
have cpW p: config_prog p -> nilp p || config_prog p by rewrite orbC => ->.
rewrite /cpmask => /cpW; elim: cp cm => [|s cp IHcp] [mr mk] cp_ok /= m_ok u.
  rewrite cpring0 /adj orbit_id has_predU unfold_in !(eq_has (fconnect_id _)).
  by case: mr mk u m_ok => [|[] [|[] []]] // [] // [].
rewrite orFb in cp_ok; case: s => // [n||] in u cp_ok m_ok *.
- set cm := Cfmask _ mk; have [/eqP Emr _] := andP m_ok.
  have{} m_ok: proper_cpmask cp cm by rewrite /= size_rotr.
  move: (cpadj_proper m_ok) {IHcp}(IHcp cm (cpW cp cp_ok) m_ok).
  case: (cpadj cm cp) => mr' mk' /andP[/eqP Emr' _] IHm.
  rewrite -(size_rotr n) -size_ring_cpmap in Emr.
  rewrite cpring_ecpR fband_cat has_cat -(rotrK n mr).
  rewrite (eq_has_r (mem_mask_rot n Emr)) /= -has_cat -IHm fband_cat.
  congr (_ || _); apply: eq_has_r; apply: mem_mask_rot.
  by rewrite size_ring_cpmap.
- have [cpQ cp'ok]: cubic_prog cp /\ nilp cp || config_prog cp.
    by case: (cp) cp_ok => // a cp1 cp1ok ; rewrite config_prog_cubic.
  have Ggt1 := cpmap_proper cpQ; set G := cpmap cp in Ggt1 u *.
  have{cpQ} plainGY := plain_ecpY G (cpmap_plain cpQ).
  have [[/eqP Emr _] nXFnG] := (andP m_ok, cface_node_ecpY G).
  have: 2 < size mr by rewrite Emr -size_ring_cpmap ltnS -size_proper_cpring.
  case: mr => [|b0 [|b1 [|b2 mr]]] // in m_ok Emr * => _.
  set cm := Cfmask _ mk; have{m_ok} cm_ok: proper_cpmask cp cm by [].
  have{IHcp cp'ok cp_ok} [] := (cpmap_simple cp_ok, IHcp cm cp'ok cm_ok).
  case: (cpadj _ _) (cpadj_proper cm_ok) => mr' mk' /andP[].
  case: Emr mr' => <- [|a0 [|a2 mr']] // _ _; rewrite [cpker _]/= cpring_ecpY.
  rewrite -/G {cm_ok}/cm head_proper_cpring // /behead map_cons.
  have [[x uFx] _ /(_ x)IHx | XFu simpleGY _] := fband_icpY u; last first.
    rewrite -(eq_has (adjF XFu)) (eq_has (adj_ecpY Ggt1)) has_cat.
    rewrite !has_mask_cons !unfold_in -(eq_has (same_cface XFu)).
    rewrite !(eq_has (@cface_ecpY _ _)) has_cat !has_mask_cons mem_head !andbF.
    rewrite -!map_mask 2!has_map !has_pred0 /= connect0 nXFnG orbT !andbT.
    rewrite -!orbA -has_cat -map_cat orbF; congr [|| _, _ | _]; symmetry.
    have:= simpleGY; rewrite [cpker _]/= 2!cat_cons (simple_catCA [::_] [::_]).
    rewrite 2!simple_cons (closed_connect (fbandF _) nXFnG) => /andP[_].
    rewrite -simple_cons -cat_cons -!map_cons -cat1s -cat_rcons -map_cat.
    rewrite -catA map_cat simple_cat andbA andbAC !has_map => /andP[_].
    apply: contraNF => /hasP[v X'v XFv]; apply/hasP; exists v => {XFv}//.
    by move: X'v; rewrite !mem_cat => /orP[]/mem_mask->; rewrite ?orbT.
  rewrite (eq_has (adjF uFx)) unfold_in {u uFx}(eq_has (same_cface uFx)).
  rewrite !has_cat !has_mask_cons (same_connect_r cfaceC nXFnG) !cface_icpY.
  rewrite (adjFr nXFnG) !adj_icpY -(cfaceC (ecpY G)) cface_ecpY andbF orFb.
  rewrite (adjC plainGY) (adj_ecpY Ggt1) -!map_mask unfold_in !has_map.
  rewrite !(eq_has (cface_icpY G x)) !(eq_has (adj_icpY G x)) -!(orbC b1).
  have:= IHx; rewrite unfold_in !has_cat !has_mask_cons /= -(orbCA (b1 && _)).
  by case: b1 => //=; do 2!case: (cface x _) => //; rewrite !andbF.
have [simpleGH [/eqP Emr Emk]] := (cpmap_simple cp_ok, andP m_ok).
rewrite /= in cp_ok; have cpQ := config_prog_cubic cp_ok.
have [Ggt1 Ggt2] := (cpmap_proper cpQ, cfmap_long cp_ok).
set G := cpmap _ in Ggt1 Ggt2 u *; have nXFnG := cface_node_ecpH Ggt1.
have{cpQ} plainGH := plain_ecpH G (cpmap_plain cpQ).
have: 2 < size mr by rewrite Emr -size_ring_cpmap -size_long_cpring.
case: mk Emk mr => // b1' mk _ [|b0 [|b1 [|b2 mr]]] // in m_ok Emr * => _.
set cm := Cfmask _ mk; have{m_ok} cm_ok: proper_cpmask cp cm by [].
have{IHcp cpW cp_ok simpleGH} [] := (simpleGH, IHcp _ (cpW _ cp_ok) cm_ok).
rewrite [cpker _]/= cpring_ecpH // (head_long_cpring Ggt2) [drop 2 _]/=.
case: (cpadj _ _) {cm_ok}(cpadj_proper cm_ok) => mr' mk' /andP[].
rewrite -{}Emr {}/cm; case: mr' => [|a0 [|a1 [|a2 mr']]] // _ _.
have [[x uFx] _ /(_ x)IHx | XFu simpleG _] := fband_icpH u; last first.
  rewrite -(eq_has (adjF XFu)) (eq_has (adj_ecpH Ggt1)) has_cat map_cons.
  rewrite !has_mask_cons !unfold_in -(eq_has (same_cface XFu)).
  rewrite has_cat !has_mask_cons connect0 (same_connect_r cfaceC nXFnG).
  rewrite !(cface_ecpH Ggt1) !(eq_has (cface_ecpH Ggt1)) !andbF.
  rewrite -!map_mask 2!has_map !has_pred0 /= !connect0 nXFnG !orbT !andbT.
  rewrite -!orbA -!(orbCA b1') -has_cat orbF !orbA; congr (_ || _); symmetry.
  have:= simpleG; rewrite (simple_catCA _ [:: _]) catA map_cons !cat_cons.
  rewrite (simple_catCA [:: _; _] [:: _]) -!map_cat simple_cons => /andP[_].
  rewrite (simple_catCA [:: _] [:: _]) -cat_rcons simple_cons.
  rewrite (closed_connect (fbandF _) nXFnG) -simple_cons -cat_cons.
  rewrite simple_cat !has_map andbA andbAC => /andP[_].
  apply: contraNF => /hasP[v X'v XFv]; apply/hasP; exists v => {XFv}//.
  by move: X'v; rewrite !mem_cat => /orP[]/mem_mask->; rewrite ?orbT.
rewrite (eq_has (adjF uFx)) unfold_in {u uFx}(eq_has (same_cface uFx)).
rewrite !has_cat map_cons !has_mask_cons (same_connect_r cfaceC nXFnG).
rewrite !cface_icpH (adjFr nXFnG) !adj_icpH -(cfaceC (ecpH G)) cface_ecpH //.
rewrite andbF (adjC plainGH) (adj_ecpH Ggt1) unfold_in -!map_mask !has_map.
rewrite !(eq_has (cface_icpH G x)) !(eq_has (adj_icpH G x)) {3}/has.
move: IHx; rewrite unfold_in !has_cat !has_mask_cons -!orbA -!(orbC b1).
rewrite -!(orbCA (b1' && _)) -2!(orbCA ((b1 || a1) && _)) -!(orbCA (b1 && _)).
by case: b1 => //=; do 3?case: (cface x _) => //; rewrite !andbF.
Qed.
