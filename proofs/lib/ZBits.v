(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Yao Li: extracted shared proofs from separate project libraries
   in this repository. *)
(* Pure-Z facts extracted without changing their statement types from:
   - proofs/openssl/bndiv/lib/Common/PropExec.v (Z_* facts);
   - proofs/glaze/binary_reflection/lib/Common/AxSymExec3Sound.v
     (testbit_mask, land_align_mask, testbit_drop_low, land_highmask).
   The original proofs are retained except for the first two: the unavailable
   Z.bounded_iff_bits_nonneg is replaced by the local high-bit argument from
   land_highmask below and Stdlib's Z.bit_log2, respectively. *)

From Stdlib Require Import ZArith Lia Bool.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma Z_testbit_high : forall n a k, (0 <= n)%Z -> (0 <= a < 2^n)%Z -> (n <= k)%Z ->
  Z.testbit a k = false.
Proof.
  intros n a k Hn Ha Hk.
  destruct (Z.testbit a k) eqn:E; [|reflexivity]. exfalso.
  apply Z.testbit_true in E; [|lia].
  assert (Hpk : (2 ^ n <= 2 ^ k)%Z) by (apply Z.pow_le_mono_r; lia).
  assert (Hsmall : (a / 2 ^ k = 0)%Z) by (apply Z.div_small; lia).
  rewrite Hsmall in E. cbn in E. lia.
Qed.

Lemma Z_bounded_by_bits : forall n a, (0 <= n)%Z -> (0 <= a)%Z ->
  (forall k, (n <= k)%Z -> Z.testbit a k = false) -> (a < 2^n)%Z.
Proof.
  intros n a Hn Ha Hb.
  destruct (Z.eq_dec a 0) as [->|Hne].
  - apply Z.pow_pos_nonneg; lia.
  - apply (proj2 (Z.log2_lt_pow2 a n ltac:(lia))).
    destruct (Z.lt_ge_cases (Z.log2 a) n) as [Hlt|Hge]; [exact Hlt|].
    pose proof (Z.bit_log2 a ltac:(lia)) as Hbit.
    rewrite Hb in Hbit by lia. discriminate.
Qed.

Lemma Z_land_range : forall a b : Z, (0 <= a < 2^64)%Z -> (0 <= b)%Z ->
  (0 <= Z.land a b < 2^64)%Z.
Proof.
  intros a b Ha Hb. split; [apply Z.land_nonneg; lia|].
  apply Z_bounded_by_bits; [lia| apply Z.land_nonneg; lia |].
  intros k Hk. rewrite Z.land_spec.
  rewrite (Z_testbit_high 64 a k) by lia. reflexivity.
Qed.

Lemma Z_lor_range : forall a b : Z, (0 <= a < 2^64)%Z -> (0 <= b < 2^64)%Z ->
  (0 <= Z.lor a b < 2^64)%Z.
Proof.
  intros a b Ha Hb. split; [apply Z.lor_nonneg; lia|].
  apply Z_bounded_by_bits; [lia| apply Z.lor_nonneg; lia |].
  intros k Hk. rewrite Z.lor_spec.
  rewrite (Z_testbit_high 64 a k) by lia.
  rewrite (Z_testbit_high 64 b k) by lia.
  reflexivity.
Qed.

Lemma Z_lxor_range : forall a b : Z, (0 <= a < 2^64)%Z -> (0 <= b < 2^64)%Z ->
  (0 <= Z.lxor a b < 2^64)%Z.
Proof.
  intros a b Ha Hb. split; [apply Z.lxor_nonneg; lia|].
  apply Z_bounded_by_bits; [lia| apply Z.lxor_nonneg; lia |].
  intros k Hk. rewrite Z.lxor_spec.
  rewrite (Z_testbit_high 64 a k) by lia.
  rewrite (Z_testbit_high 64 b k) by lia.
  reflexivity.
Qed.

Lemma Z_shiftr_range : forall a k : Z, (0 <= a < 2^64)%Z -> (0 <= k)%Z ->
  (0 <= Z.shiftr a k < 2^64)%Z.
Proof.
  intros a k Ha Hk. rewrite Z.shiftr_div_pow2 by lia.
  pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) Hk).
  split; [apply Z.div_pos; lia|].
  apply Z.le_lt_trans with a; [|lia].
  apply Z.div_le_upper_bound; nia.
Qed.

Lemma testbit_mask : forall j i, (0 <= j)%Z -> (j < 64)%Z -> (0 <= i)%Z ->
  Z.testbit (2 ^ 64 - 2 ^ j) i = ((j <=? i) && (i <? 64))%Z.
Proof.
  intros j i Hj Hj64 Hi.
  assert (Heq : (2 ^ 64 - 2 ^ j)%Z = Z.shiftl (Z.ones (64 - j)) j).
  { rewrite Z.shiftl_mul_pow2 by lia. unfold Z.ones. rewrite Z.shiftl_1_l.
    rewrite <- Z.sub_1_r, Z.mul_sub_distr_r, <- Z.pow_add_r by lia.
    replace (64 - j + j)%Z with 64%Z by lia. lia. }
  rewrite Heq.
  destruct (Z.lt_ge_cases i j) as [Hlt|Hge].
  - rewrite Z.shiftl_spec_low by lia. symmetry. apply andb_false_intro1. apply Z.leb_gt. lia.
  - rewrite Z.shiftl_spec_high by lia. rewrite Z.testbit_ones by lia.
    destruct (Z.lt_ge_cases i 64) as [Hi64|Hi64].
    + replace (j <=? i)%Z with true by (symmetry; apply Z.leb_le; lia).
      replace (i <? 64)%Z with true by (symmetry; apply Z.ltb_lt; lia).
      apply andb_true_intro. split; [apply Z.leb_le; lia | apply Z.ltb_lt; lia].
    + replace (i <? 64)%Z with false by (symmetry; apply Z.ltb_ge; lia). rewrite andb_false_r.
      apply andb_false_intro2. apply Z.ltb_ge. lia.
Qed.

Lemma land_align_mask : forall x j, (0 <= j)%Z -> (j < 64)%Z -> (0 <= x < 2 ^ 64)%Z ->
  (x mod 2 ^ j = 0)%Z -> Z.land x (2 ^ 64 - 2 ^ j) = x.
Proof.
  intros x j Hj Hj64 Hx Hmod.
  assert (Hx' : x = ((x / 2 ^ j) * 2 ^ j)%Z).
  { pose proof (Z.div_mod x (2 ^ j) ltac:(apply Z.pow_nonzero; lia)) as Hdm. lia. }
  apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, testbit_mask by lia.
  destruct (Z.lt_ge_cases i j) as [Hlt|Hge].
  - replace (j <=? i)%Z with false by (symmetry; apply Z.leb_gt; lia).
    rewrite andb_false_r. rewrite Hx'. symmetry. apply Z.mul_pow2_bits_low. lia.
  - replace (j <=? i)%Z with true by (symmetry; apply Z.leb_le; lia).
    destruct (Z.lt_ge_cases i 64) as [Hi64|Hi64].
    + replace (i <? 64)%Z with true by (symmetry; apply Z.ltb_lt; lia). apply andb_true_r.
    + replace (i <? 64)%Z with false by (symmetry; apply Z.ltb_ge; lia). rewrite andb_false_r.
      symmetry. apply (Z_testbit_high 64 x i); lia.
Qed.

Local Open Scope Z_scope.

Lemma testbit_drop_low : forall q r j i, 0 <= j -> 0 <= r < 2 ^ j -> j <= i ->
  Z.testbit (q * 2 ^ j + r) i = Z.testbit (q * 2 ^ j) i.
Proof.
  intros q r j i Hj Hr Hi.
  replace i with ((i - j) + j) by lia.
  rewrite <- !Z.div_pow2_bits by lia.
  f_equal. rewrite Z.div_add_l by lia. rewrite (Z.div_small r) by lia.
  rewrite Z_div_mult by lia. lia.
Qed.

Lemma land_highmask : forall x j, 0 <= j < 64 -> 0 <= x < 2 ^ 64 ->
  Z.land x (2 ^ 64 - 2 ^ j) = x - x mod 2 ^ j.
Proof.
  intros x j Hj Hx.
  assert (Hp : 0 < 2 ^ j) by (apply Z.pow_pos_nonneg; lia).
  pose proof (Z.div_mod x (2 ^ j) ltac:(lia)) as Hdm.
  pose proof (Z.mod_pos_bound x (2 ^ j) Hp) as Hmb.
  set (q := x / 2 ^ j) in *. set (r := x mod 2 ^ j) in *.
  replace (x - r) with (q * 2 ^ j) by lia. rewrite Hdm.
  replace (2 ^ j * q + r) with (q * 2 ^ j + r) by lia.
  apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec.
  pose proof (testbit_mask j i ltac:(lia) ltac:(lia) ltac:(lia)) as Hmask.
  rewrite Hmask. destruct (Z.lt_ge_cases i j) as [Hij|Hij].
  - replace (j <=? i) with false by (symmetry; apply Z.leb_gt; lia). rewrite andb_false_r.
    symmetry. apply Z.mul_pow2_bits_low. lia.
  - replace (j <=? i) with true by (symmetry; apply Z.leb_le; lia).
    destruct (Z.lt_ge_cases i 64) as [Hi64|Hi64].
    + replace (i <? 64) with true by (symmetry; apply Z.ltb_lt; lia). rewrite andb_true_r.
      apply testbit_drop_low; lia.
    + replace (i <? 64) with false by (symmetry; apply Z.ltb_ge; lia). rewrite andb_false_r.
      assert (0 <= q) by (subst q; apply Z.div_pos; lia).
      assert (0 <= q * 2 ^ j < 2 ^ 64) by nia.
      destruct (Z.testbit (q * 2 ^ j) i) eqn:Ht; [|reflexivity]. exfalso.
      assert (Hb : forall n a, 0 <= n -> 0 <= a < 2 ^ n -> forall k, n <= k -> Z.testbit a k = false).
      { intros n a Hn Ha k Hk. destruct (Z.testbit a k) eqn:E; [|reflexivity]. exfalso.
        apply Z.testbit_true in E; [|lia].
        assert (Hpk : 2 ^ n <= 2 ^ k) by (apply Z.pow_le_mono_r; lia).
        assert (Hsmall : a / 2 ^ k = 0) by (apply Z.div_small; lia). rewrite Hsmall in E. cbn in E. lia. }
      rewrite (Hb 64 (q * 2 ^ j)) in Ht by lia. discriminate.
Qed.
