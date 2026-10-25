(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.Shared Require PlacementSearch.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Placement.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_MmapComplete () := "C46Stdlib5Lists4List2hdK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C5ARocqVerifyHarness?AgentSubmission3Lib9Placement:vm_base_okC47Corelib4Init9Datatypes4andbI47Corelib4Init5Logic3and00C46Stdlib4Bool4Bool=andb_true_iffC45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z3addC4ELinuxProcessSemantics?LinuxProcessSem5State9alloc_topC56Stdlib6ZArith6BinInt1Z3lebI47Corelib4Init9Datatypes4prod00C4ELinuxProcessSemantics?LinuxProcessSem5State;vm_reservedC4ELinuxProcessSemantics?LinuxProcessSem5State7vm_mapsC47Corelib4Init9Datatypes3appC45stdpp9bitvector;definitions7Z_to_bvC4ELinuxProcessSemantics?LinuxProcessSem5State;region_freeC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3eqbI47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z6eqb_eqC56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z6ltb_ltC56Stdlib6ZArith6BinInt1Z6leb_leK47Corelib4Init5Logic3and01C56Stdlib6ZArith6BinInt1Z6moduloI47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C4ELinuxProcessSemantics?LinuxProcessSem5State9page_sizeK47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00I4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes6option00C5ARocqVerifyHarness?AgentSubmission3Lib9Placement<vm_find_baseK47Corelib4Init9Datatypes6option01K47Corelib4Init5Logic2eq01C47Corelib4Init5Logic8eq_ind_rC5ARocqVerifyHarness?AgentSubmission3Lib9Placement@vm_gap_availableK47Corelib4Init9Datatypes4bool02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3divC46Stdlib6ZArith4Zdiv:Z_mod_multC4ELinuxProcessSemantics?LinuxProcessSem5State?page_round_up_ZK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula07C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3mulC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula03K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init5Logic5False00K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op203C56Stdlib6ZArith6BinInt1ZBdiv_lt_upper_boundC56Stdlib6ZArith6BinInt1ZDmul_le_mono_nonneg_rK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C56Stdlib6ZArith6BinInt1Z8le_transC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K46Stdlib9micromega5Tauto8GFormula06C47Corelib4Init9Datatypes8list_indC46Stdlib5Lists4List9fold_leftC46Stdlib5Lists4List2InC47Corelib4Init5Logic9False_indc5?OssFuzzTheorems6Proofs6Shared?PlacementSearch@fold_max_ge_seedK47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C46Stdlib5Lists4List4findI47Corelib4Init5Logic2ex00K47Corelib4Init5Logic2ex01C47Corelib4Init5Logic6eq_symC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic6eq_indI47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01C4ELinuxProcessSemantics?LinuxProcessSem5State<alloc_top_ltC45stdpp9bitvector;definitions:bv_modulusC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith6BinInt1Z3powC46Stdlib9micromega;ZifyClasses6eq_iffC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega7EnvRing5PExpr07C45stdpp9bitvector;definitions7bv_wrapC45stdpp9bitvector;definitions=bv_wrap_smallC45stdpp9bitvector;definitions@Z_to_bv_unsignedK46Stdlib9micromega:ZMicromega;ZArithProof03C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC46Stdlib5Lists4List6filterC46Stdlib5Lists4List9filter_InC47Corelib4Init5Logic3iffc5?OssFuzzTheorems6Proofs6Shared?PlacementSearch;fold_max_lec5?OssFuzzTheorems6Proofs6Shared?PlacementSearchCfold_max_in_or_seedC47Corelib4Init5Logic5proj1C47Corelib5Lists7ListDef3mapC46Stdlib5Lists4List:in_map_iffc5?OssFuzzTheorems6Proofs6Shared?PlacementSearchGpage_round_up_Z_alignedK47Corelib4Init9Datatypes4prod01C4ELinuxProcessSemantics?LinuxProcessSem5State>region_free_InC4ELinuxProcessSemantics?LinuxProcessSem5State:iv_overlapC46Stdlib4Bool4Bool>andb_false_iffC56Stdlib6ZArith6BinInt1Z;le_gt_casesc5?OssFuzzTheorems6Proofs6Shared?PlacementSearchBpage_round_up_Z_lec5?OssFuzzTheorems6Proofs6Shared?PlacementSearch>fold_max_ge_inc5?OssFuzzTheorems6Proofs6Shared?PlacementSearchBpage_round_up_Z_geC56Stdlib6ZArith6BinInt1Z6ltb_geC56Stdlib6ZArith6BinInt1Z7le_reflC56Stdlib6ZArith6BinInt1Z;add_le_monoC4ELinuxProcessSemantics?LinuxProcessSem5StateAregion_free_introC5ARocqVerifyHarness?AgentSubmission3Lib9PlacementBvm_base_candidatesC47Corelib4Init5Logic5proj2c5ARocqVerifyHarness?AgentSubmission3Lib<MmapCompleteBvm_base_find_of_InC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C4ELinuxProcessSemantics?LinuxProcessSem5State:two_pow_64I47Corelib7Numbers7BinNums1N00C46Stdlib9micromega8ZifyInst7Inj_Z_ZC46Stdlib5Lists4List8map_consc5ARocqVerifyHarness?AgentSubmission3Lib<MmapCompleteEvm_find_base_completec5ARocqVerifyHarness?AgentSubmission3Lib<MmapCompleteJvm_find_base_gap_available".
(* [comment removed for export] *)
Unset Lia Cache.
Unset Nia Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma vm_base_ok_sound : forall h nZ a,
  vm_base_ok h nZ a = true ->
  (bv_unsigned a mod page_size = 0)%Z
  /\ (0 < bv_unsigned a)%Z
  /\ (bv_unsigned a + nZ <= alloc_top h)%Z
  /\ region_free (vm_reserved h ++ vm_maps h) a (Z_to_bv 64 nZ) = true.
Proof.
  intros h nZ a H. unfold vm_base_ok in H.
  apply andb_true_iff in H as [H Hfree].
  apply andb_true_iff in H as [H Hceil].
  apply andb_true_iff in H as [Halign Hpos].
  apply Z.eqb_eq in Halign. apply Z.ltb_lt in Hpos. apply Z.leb_le in Hceil.
  repeat split; assumption.
Qed.

Lemma vm_find_base_gap_available : forall h nZ a,
  vm_find_base h nZ = Some a -> vm_gap_available h nZ = true.
Proof. intros h nZ a H. unfold vm_gap_available. now rewrite H. Qed.

(* [comment removed for export] *)




(* [comment removed for export] *)










Lemma vm_base_find_of_In : forall {A} (f : A -> bool) l x,
  In x l -> f x = true -> exists y, List.find f l = Some y.
Proof.
ltac2:(KReplay.run1 (kr_t_MmapComplete ()) [] "p'0h01yh12Hyh21xh33Hinh41lh51Hh62Hxh71Ah83Heqh92IHh:1bi001bh;1eh<1fp;1p;3p;2p;4p;6p;7p;5p200R0g00mHR1p4p710p8P0g00FAR2p4p710p8P0g00lHR3p4p710p8P0g0103R4p4p710p8g00KXj18TP1j35Tg00Cdj12TP4j34Tg00EEj21Tg00<Bj30Tg010Lj23Tg00K8j1<Tg00m_j2;Tg00Y`j3:Tg00Egj29Tg010fj4=Tg011@j4BTg011\j6ATg012:j6@TP2j7?TP3j5>Tg00?TR3f0R2g00@4R430p=6g00GbR19032p=7P3\2f1R5#8f2R6%86f3R7f4R8?525P8P5O1#6f6R9f7R:#2A4:9811:230X09'3[[]2W4%<79572P7P5O1#6f5R;%29%<9949;119230X0;'3/;5W6W3X26%87A5;25P;P5O1#6f8R<#2A4<:811<230X0:,3:[[^28A:9769592P9P5O1#6P:P;O1P31932P<P9O1=032P3f:R7P<O1=032f<R=f=R>#2R?P3f>#2P611>7f9R@94>=RAn010000002000011>2RB30X0='3]1P5P@P:O1R5#6f;RC%2=11=@11=230X0CP<%2C11C<'9C=W1%75g00kJA0C<;A5C;:A0?ABX0=,3=P8A0=@9P>P:P>P2O1#7f?R8f@RB#2A4B8=11B230X08'3]1X0>P=P:O1#7P3P1P>P<O1R8P4P3P8P1P2CBP9EAA0314P3P1P3p-0P2g00d1R1g012Vn0110000020000X;3g0132P4P2E@P1fAR1#2A41B>111230X0B,3B/;2b5b8W1P7P2P6F?W5P2O1A5=9<P<P:P2P;O3W3P2O1n200100000021000010000W1n0110000020000P2O1b1b:%2@A:@9;94@<11@230X0<,3<eW6W3X2;W9W4X06P2D>W4W<X70o"). Qed.

Lemma vm_find_base_complete : forall h nZ g,
  (0 <= nZ)%Z ->
  (bv_unsigned g mod page_size = 0)%Z ->
  (0 < bv_unsigned g)%Z ->
  (bv_unsigned g + nZ <= alloc_top h)%Z ->
  region_free (vm_reserved h ++ vm_maps h) g (Z_to_bv 64 nZ) = true ->
  exists a, vm_find_base h nZ = Some a.
Proof.
  intros h nZ g HnPos HgAl HgPos Hghi Hgfree.
  pose proof (alloc_top_lt h) as Htop.
  assert (Hmod : two_pow_64 = bv_modulus 64) by reflexivity.
  set (maps := vm_reserved h ++ vm_maps h) in *.
  set (G := bv_unsigned g) in *.
  assert (HG : (0 <= G < bv_modulus 64)%Z)
    by (subst G; rewrite <- Hmod; pose proof (bv_unsigned_in_range 64 g);
        unfold bv_modulus in *; unfold two_pow_64; lia).
  assert (HnW : bv_unsigned (Z_to_bv 64 nZ) = nZ)
    by (rewrite Z_to_bv_unsigned; apply bv_wrap_small; rewrite <- Hmod; lia).
  assert (Hfloor : (page_size <= G)%Z).
  { unfold page_size in *.
    pose proof (Z.div_mod G 4096 ltac:(lia)) as Hdm.
    pose proof (Z.mod_pos_bound G 4096 ltac:(lia)). nia. }
  set (cZ := page_size
             :: map (fun iv : word * word =>
                       page_round_up_Z (bv_unsigned (fst iv) + bv_unsigned (snd iv)))
                    maps).
  set (cs := List.filter (fun c => (c <=? G)%Z) cZ).
  set (g' := fold_left Z.max cs page_size).
  assert (Hcs : forall x, In x cs <-> In x cZ /\ (x <=? G)%Z = true)
    by (intro x0; unfold cs; exact (filter_In _ x0 _)).
  assert (Hlo : (page_size <= g')%Z) by (unfold g'; apply OssFuzzTheorems.Proofs.Shared.PlacementSearch.fold_max_ge_seed).
  assert (Hhi : (g' <= G)%Z).
  { unfold g'. apply OssFuzzTheorems.Proofs.Shared.PlacementSearch.fold_max_le; [exact Hfloor|]. intros x Hx.
    apply Hcs in Hx. destruct Hx as [_ Hx]. now apply Z.leb_le. }
  assert (Hcand : In g' cZ).
  { destruct (OssFuzzTheorems.Proofs.Shared.PlacementSearch.fold_max_in_or_seed cs page_size) as [Heq|Hin].
    - assert (Heq' : g' = page_size) by exact Heq. rewrite Heq'. now left.
    - apply Hcs in Hin. exact (proj1 Hin). }
  assert (Hg'W : bv_unsigned (Z_to_bv 64 g') = g')
    by (rewrite Z_to_bv_unsigned; apply bv_wrap_small; unfold page_size in Hlo; lia).
  assert (Hg'Al : (g' mod page_size = 0)%Z).
  { destruct Hcand as [Heq|Hin].
    - rewrite <- Heq. reflexivity.
    - apply in_map_iff in Hin. destruct Hin as (p & Heq & _).
      rewrite <- Heq. apply OssFuzzTheorems.Proofs.Shared.PlacementSearch.page_round_up_Z_aligned. }
  assert (Hg'free : region_free maps (Z_to_bv 64 g') (Z_to_bv 64 nZ) = true).
  { apply region_free_intro. intros b s Hin.
    pose proof (region_free_In _ _ _ _ _ Hgfree Hin) as Hno.
    unfold iv_overlap in *. rewrite HnW in Hno. fold G in Hno.
    rewrite Hg'W, HnW.
    apply andb_false_iff in Hno.
    set (B := bv_unsigned b) in *. set (S := bv_unsigned s) in *.
    destruct (Z.le_gt_cases (B + S) G) as [Hend|Hend].
    -
      assert (Hc : In (page_round_up_Z (B + S)) cZ).
      { right. apply in_map_iff. exists (b, s).
        split; [reflexivity|assumption]. }
      assert (Hcle : (page_round_up_Z (B + S) <= G)%Z)
        by (apply OssFuzzTheorems.Proofs.Shared.PlacementSearch.page_round_up_Z_le; assumption).
      assert (Hcg' : (page_round_up_Z (B + S) <= g')%Z).
      { unfold g'. apply OssFuzzTheorems.Proofs.Shared.PlacementSearch.fold_max_ge_in. apply Hcs. split; [assumption|].
        now apply Z.leb_le. }
      pose proof (OssFuzzTheorems.Proofs.Shared.PlacementSearch.page_round_up_Z_ge (B + S)) as Hround.
      apply andb_false_iff. left. apply Z.ltb_ge.
      exact (Z.le_trans _ _ _ Hround Hcg').
    -
      destruct Hno as [Hno|Hno].
      + apply Z.ltb_ge in Hno. lia.
      + apply Z.ltb_ge in Hno.
        apply andb_false_iff. right. apply Z.ltb_ge.
        exact (Z.le_trans _ _ _
                 (Z.add_le_mono _ _ _ _ Hhi (Z.le_refl nZ)) Hno). }
  unfold vm_find_base.
  apply (vm_base_find_of_In (vm_base_ok h nZ) _ (Z_to_bv 64 g')).
  - unfold vm_base_candidates. fold maps.
    destruct Hcand as [Heq|Hin].
    + left. now rewrite Heq.
    + right. apply in_map_iff in Hin. destruct Hin as (p & Heq & Hp).
      apply in_map_iff. exists p. split; [now rewrite Heq|exact Hp].
  - unfold vm_base_ok. fold maps. rewrite Hg'W, Hg'free.
    rewrite (proj2 (Z.eqb_eq _ _) Hg'Al).
    assert (Hg'base : (g' + nZ <= alloc_top h)%Z)
      by exact (Z.le_trans _ _ _ (Z.add_le_mono _ _ _ _ Hhi (Z.le_refl nZ)) Hghi).
    rewrite (proj2 (Z.leb_le _ _) Hg'base).
    assert (Hg'pos : (0 < g')%Z) by (unfold page_size in Hlo; lia).
    rewrite (proj2 (Z.ltb_lt _ _) Hg'pos).
    reflexivity.
Qed.

(* [comment removed for export] *)
Lemma vm_gap_available_complete : forall h nZ g,
  (0 <= nZ)%Z ->
  (bv_unsigned g mod page_size = 0)%Z ->
  (0 < bv_unsigned g)%Z ->
  (bv_unsigned g + nZ <= alloc_top h)%Z ->
  region_free (vm_reserved h ++ vm_maps h) g (Z_to_bv 64 nZ) = true ->
  vm_gap_available h nZ = true.
Proof.
  intros h nZ g Hn Hal Hpos Hhi Hfree.
  destruct (vm_find_base_complete h nZ g Hn Hal Hpos Hhi Hfree) as [a Ha].
  exact (vm_find_base_gap_available _ _ _ Ha).
Qed.
