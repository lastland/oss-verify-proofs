(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX.
From OssFuzzTheorems.Proofs.simdjson.fuzz_ondemand.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_ondemand.lib.MallocP Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_ondemand.lib.Spec Require Import Prelim STree Malloc Monad Stdio SjModel Target Driver Prog StrFun.
From OssFuzzTheorems.Proofs.simdjson.fuzz_ondemand.lib.P Require Import Layout Exit Printf_stdio_iface Sj_iface Driver_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_ondemand.lib.P Require Export Sj_kit.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Notation psegs := Image.psegs.
Notation mem := (word -> option byte).
Notation wz := MallocRep.wz.

From OssFuzzTheorems.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.simdjson.fuzz_ondemand.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].
Local Ltac std_nia__ := nia.
Local Ltac nia := first [std_nia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_nia__].
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Lemma agree_of_drv_pres : forall LB SP m m', rdrv_pres LB SP m m' -> agree_on (lx_client LB SP DRVW) m m'.
Proof. intros LB SP m m' H. exact H. Qed.



Lemma bytes_at_read1 : forall m A bs (i : Z) b a,
  bytes_at psegs m A bs -> 0 <= i -> nth_error bs (Z.to_nat i) = Some b -> a = wa (A + i) ->
  ov_read_bytes psegs m a 1 = Some [b].
Proof.
  intros m A bs i b a HB Hi Hn ->.
  destruct (@nth_error_split _ bs (Z.to_nat i) b Hn) as (l1 & l2 & E & Hl1).
  replace i with (Z.of_nat (Z.to_nat i)) at 1 by lia.
  rewrite (bytes_at_ov_read psegs m A bs (Z.to_nat i) 1 HB) by (rewrite E, length_app; cbn; lia).
  f_equal. rewrite E at 1. rewrite skipn_app, skipn_all2, Hl1, Nat.sub_diag by lia. reflexivity.
Qed.


Lemma to_bytes_nth : forall (l : list Z) i c, nth_error l i = Some c -> nth_error (to_bytes l) i = Some (Z_to_bv 8 c).
Proof. intros l i c H. unfold to_bytes. rewrite nth_error_map, H. reflexivity. Qed.

Lemma znth_nth_error : forall (l : list Z) (i : Z), 0 <= i < zlength l -> nth_error l (Z.to_nat i) = Some (znth l i).
Proof.
  intros l i Hi. unfold znth, zlength in *. replace (i <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
  destruct (nth_error l (Z.to_nat i)) as [x|] eqn:E.
  - f_equal. symmetry. apply nth_error_nth. exact E.
  - apply nth_error_None in E. lia.
Qed.

Fixpoint tall {R} (P : R -> Prop) (t : itree node (exc R)) : Prop :=
  match t with
  | Ret Unr => True
  | Ret (Ok r) => P r
  | Vis _ k => forall rsp, tall P (k rsp)
  | Cho k => forall z, tall P (k z)
  end.

Lemma tall_mono : forall {R} (P P' : R -> Prop) t, tall P t -> (forall r, P r -> P' r) -> tall P' t.
Proof.
  induction t as [[|r]|n k IH|kc IHc]; cbn; intros H HP.
  - exact I.
  - apply HP. exact H.
  - intros rsp. eapply IH; [apply H| exact HP].
  - intros z. eapply IHc; [apply H| exact HP].
Qed.

Lemma tall_ebind : forall {A B} (P : A -> Prop) (Q : B -> Prop) (t : itree node (exc A)) (f : A -> itree node (exc B)),
  tall P t -> (forall a, P a -> tall Q (f a)) -> tall Q (ebind t f).
Proof.
  induction t as [[|a]|n k IH|kc IHc]; cbn; intros f H HF; [exact I| apply HF; exact H| |intros z; apply IHc; [apply H| exact HF]].
  intros rsp. apply IH; [apply H| exact HF].
Qed.

Lemma impl_tall : forall {R} (t : itree node (exc R)) (P : R -> Prop) (Q : R -> machine_state -> Prop) ms,
  impl psegs (at_node psegs) t (epost Q) ms -> tall P t ->
  impl psegs (at_node psegs) t (epost (fun r ms' => Q r ms' /\ P r)) ms.
Proof.
  intros R t. induction t as [[|r]|n k IH|kc IHc]; cbn; intros P Q ms H HP.
  - exact H.
  - eapply evt_mono; [exact H|]. cbn. intros ms' HQ. split; [exact HQ| exact HP].
  - eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. apply IH; [apply Hk| apply HP].
  - destruct H as [z H]. exists z. apply IHc; [exact H| apply HP].
Qed.

Section Keeps.
  Context {St B : Type} (f : St -> B).

  Definition keeps {A} (c : M St A) : Prop := forall s, tall (fun p => f (snd p) = f s) (c s).

  Lemma keeps_ret : forall {A} (a : A), keeps (mret a).
  Proof. intros A a s. reflexivity. Qed.
  Lemma keeps_unr : forall {A}, keeps (munr (A:=A)).
  Proof. intros A s. exact I. Qed.
  Lemma keeps_get : keeps mget.
  Proof. intros s. reflexivity. Qed.
  Lemma keeps_upd : forall g, (forall s, f (g s) = f s) -> keeps (mupd g).
  Proof. intros g Hg s. cbn. apply Hg. Qed.
  Lemma keeps_sys : forall {A} n (dec : resp -> option A), keeps (msys n dec).
  Proof. intros A n dec s. cbn. intros rsp. destruct (dec rsp); cbn; [reflexivity| exact I]. Qed.
  Lemma keeps_bind : forall {A C} (m : M St A) (k : A -> M St C), keeps m -> (forall a, keeps (k a)) -> keeps (mbind m k).
  Proof.
    intros A C m k Hm Hk s. unfold mbind. eapply tall_ebind; [apply Hm|]. cbn. intros [a s1] E. cbn in E.
    eapply tall_mono; [apply Hk|]. cbn. intros [c s2] E2. cbn in E2 |- *. congruence.
  Qed.
  Lemma keeps_getk : forall {C} (k : St -> M St C), (forall s0, keeps (k s0)) -> keeps (mbind mget k).
  Proof. intros C k Hk s. unfold mbind, mget. cbn. apply Hk. Qed.
  Lemma keeps_loop : forall {X R} fuel (body : X -> M St (X + R)), (forall x, keeps (body x)) -> forall x, keeps (mloop fuel body x).
  Proof.
    induction fuel as [|fuel IH]; intros body HB x; cbn; [apply keeps_unr|].
    apply keeps_bind; [apply HB|]. intros [x'|r]; [apply IH; exact HB| apply keeps_ret].
  Qed.
  Lemma keeps_if : forall {A} (b : bool) (m1 m2 : M St A), keeps m1 -> keeps m2 -> keeps (if b then m1 else m2).
  Proof. intros A [|] m1 m2 H1 H2; assumption. Qed.
End Keeps.
Arguments keeps {St B} f {A} c.

End WithCeiling0.
Ltac keeps_step :=
  first [ apply keeps_ret | apply keeps_unr | apply keeps_sys | apply keeps_get
        | apply keeps_getk | apply keeps_bind | apply keeps_if
        | apply keeps_upd; [intros; reflexivity] ].
Ltac keeps_tac :=
  repeat (intros; cbn beta;
          first [ solve [auto]
                | keeps_step
                | lazymatch goal with
                  | |- keeps _ (match ?x with _ => _ end) => destruct x
                  end ]).

Section WithCeiling1. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Lemma implM_keepsf : forall {B A} (f : PState -> B) (c : M PState A) s Q ms,
  implM psegs c s Q ms -> keeps f c -> implM psegs c s (fun r s' ms' => Q r s' ms' /\ f s' = f s) ms.
Proof.
  intros B A0 f c s Q ms H K. unfold implM in *.
  eapply impl_epost_mono; [eapply impl_tall; [exact H| apply K]|]. cbn. intros [a s'] ms' [HQ E]. split; [exact HQ| exact E].
Qed.

Definition but_so (s : PState) : PState := set_so_ps stdout_init s.

Lemma upd_so_keeps : forall g, keeps but_so (upd_so ps_so set_so_ps g).
Proof. intros g. unfold upd_so. apply keeps_upd. intros [? ? ? ?]; reflexivity. Qed.

Lemma stdio_writev_keeps : forall fd buf s0, keeps but_so (stdio_writev (St:=PState) fd buf s0).
Proof. intros fd buf s0. unfold stdio_writev. apply keeps_loop. intros x. unfold wv_body. keeps_tac. Qed.

Lemma stdout_writefn_keeps : forall l, keeps but_so (stdout_writefn ps_so set_so_ps l).
Proof.
  intros l. unfold stdout_writefn, stdout_stdio_write, rd_so. pose proof upd_so_keeps. pose proof stdio_writev_keeps. keeps_tac.
Qed.

Lemma stdout_vprintf_keeps : forall ps, keeps but_so (stdout_vprintf ps_so set_so_ps ps).
Proof.
  intros ps. unfold stdout_vprintf, stdout_towrite. apply keeps_bind; [apply upd_so_keeps|]. intros _.
  induction ps as [|pc ps IH]; cbn [out_pieces]; [apply keeps_ret|].
  apply keeps_bind; [| intros; exact IH].
  unfold stdout_fwritex, stdout_towrite, rd_so. pose proof upd_so_keeps. pose proof stdout_writefn_keeps. keeps_tac.
Qed.

Lemma but_so_eq : forall s s', but_so s' = but_so s -> ps_m s' = ps_m s /\ ps_brk s' = ps_brk s /\ ps_fa s' = ps_fa s.
Proof. intros [? ? ? ?] [? ? ? ?] E. unfold but_so, set_so_ps in E. cbn in E. injection E as -> -> ->. cbn. auto. Qed.

Definition RHEAP_frame_stmt : Prop := forall s LB m m' W,
  RHEAP s LB m -> munch W m m' -> wmono psegs m m' -> Forall (rclient_write_ok LB) W -> RHEAP s LB m'.
Definition RHEAP_block_range_stmt : Prop := forall s LB m b, RHEAP s LB m -> In b LB -> rblock_range (blk_addr b) (blk_size b).
Definition RHEAP_blocks_nodup_stmt : Prop := forall s LB m, RHEAP s LB m -> List.NoDup (map blk_id LB).
Definition RHEAP_blocks_disjoint_stmt : Prop := forall s LB m b1 b2,
  RHEAP s LB m -> In b1 LB -> In b2 LB -> blk_id b1 <> blk_id b2 ->
  blk_addr b1 + blk_size b1 <= blk_addr b2 \/ blk_addr b2 + blk_size b2 <= blk_addr b1.


Lemma bptr_eqb_eq : forall p q : bptr, bptr_eqb p q = true <-> p = q.
Proof.
  intros [[r o] z] [[r' o'] z']. unfold bptr_eqb, aptr_eqb. cbn [fst snd].
  rewrite !andb_true_iff, N.eqb_eq, !Z.eqb_eq. split; [intros [[-> ->] ->]; reflexivity| intros E; injection E as -> -> ->; auto].
Qed.

Lemma lb_remove_head : forall pb D n LB, List.NoDup (map blk_id ((pb, D, n) :: LB)) -> lb_remove pb ((pb, D, n) :: LB) = LB.
Proof.
  intros pb D n LB ND. cbn [map] in ND. inversion ND as [|x l NI ND']; subst. clear ND.
  unfold lb_remove. cbn. replace (bptr_eqb pb pb) with true by (symmetry; apply bptr_eqb_eq; reflexivity). cbn.
  induction LB as [|b LB IH]; [reflexivity|]. cbn.
  destruct (bptr_eqb (blk_id b) pb) eqn:E.
  - exfalso. apply NI. left. apply bptr_eqb_eq in E. exact E.
  - cbn. f_equal. apply IH; [intros Hin; apply NI; right; exact Hin| inversion ND'; assumption].
Qed.
End WithCeiling1.
