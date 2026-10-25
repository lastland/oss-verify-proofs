(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.Shared Require PlacementSearch.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Cfg.
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
  intros A f l. induction l as [|y l IH]; intros x Hin Hx; [contradiction|].
  cbn. destruct (f y) eqn:Hy; [now exists y|].
  destruct Hin as [->|Hin]; [congruence|]. exact (IH x Hin Hx).
Qed.

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
  (* [comment removed for export] *)
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
    - (* [comment removed for export] *)
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
    - (* [comment removed for export] *)
      destruct Hno as [Hno|Hno].
      + apply Z.ltb_ge in Hno. lia.
      + apply Z.ltb_ge in Hno.
        apply andb_false_iff. right. apply Z.ltb_ge.
        exact (Z.le_trans _ _ _
                 (Z.add_le_mono _ _ _ _ Hhi (Z.le_refl nZ)) Hno). }
  (* [comment removed for export] *)
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
