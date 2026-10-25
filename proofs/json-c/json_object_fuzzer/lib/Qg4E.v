(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase State.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QU8l.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

From OssFuzzTheorems.Proofs.Shared Require PlacementSearch.

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QU8l.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QU8l.

Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Definition is_exit_no (no : word) : Prop :=
bv_unsigned no = 93%Z \/ bv_unsigned no = 94%Z.

Section WithSegs.
Variable segs : list Segment.
Variable code : word.

Inductive to_exit : machine_state -> Prop :=
| te_here : forall ms x8,
ms_svc_pending ms = Some x8 ->
is_exit_no x8 ->
ms_gpr ms 0 = code ->
to_exit ms
| te_step : forall ms ms',
ms_svc_pending ms = None ->
RiscvSemantics.step segs ms = MachineOk ms' ->
to_exit ms' ->
to_exit ms.

Fixpoint sim_c (fuel : nat) (ms : machine_state) : bool :=
match fuel with
| O => false
| S fuel' =>
match ms_svc_pending ms with
| Some x8 => ((bv_unsigned x8 =? 93)%Z || (bv_unsigned x8 =? 94)%Z)
&& bv_eqb (ms_gpr ms 0) code
| None =>
match RiscvSemantics.step segs ms with
| MachineOk ms' => sim_c fuel' ms'
| MachineFault | MachineUnmodeled => false
end
end
end.

Lemma sstep_instr_inv : forall ms model ms' evs st,
m_vm_lazy model = [] ->
ms_svc_pending ms = None ->
RiscvSemantics.step segs ms = MachineOk ms' ->
sstep segs (mkCfg ms model) evs st ->
evs = [] /\ st = SNext (mkCfg ms' model).
Proof.
intros ms model ms' evs st Hlazy Hsvc Hstep Hss.
inversion Hss; subst.
-
match goal with H : mi_account_step segs ms model = MachineOk _ |- _ =>
rewrite (mi_account_step_no_lazy segs ms model Hlazy) in H;
rewrite Hstep in H; inversion H; subst end.
split; reflexivity.
-
match goal with H : mi_account_step segs ms model = MachineFault |- _ =>
rewrite (mi_account_step_no_lazy segs ms model Hlazy) in H;
rewrite Hstep in H; discriminate end.
-
match goal with H : mi_account_step segs ms model = MachineUnmodeled |- _ =>
rewrite (mi_account_step_no_lazy segs ms model Hlazy) in H;
rewrite Hstep in H; discriminate end.
-  congruence.
-  congruence.
-  congruence.
-  congruence.
-  congruence.
Qed.

Lemma star_halted_nil : forall c tr c',
m_halted (cfg_model c) <> None -> star segs c tr c' -> tr = [] /\ c' = c.
Proof.
intros c tr c' Hh Hstar. inversion Hstar as [|c1 evs c2 tr2 c3 Hss Hstar2]; subst.
- split; reflexivity.
- exfalso. destruct c as [ms model]. cbn in Hh.
inversion Hss; subst; cbn in Hh; congruence.
Qed.

Definition exit_post (fs : Fs.Fs) : post :=
fun tr o => tr = [ExitEv (bv_and code (Z_to_bv 64 255)) fs]
/\ exits_with (bv_and code (Z_to_bv 64 255)) tr o.

Definition on_path (c : config) : Prop :=
(m_halted (cfg_model c) = None /\ m_vm_lazy (cfg_model c) = [] /\
to_exit (cfg_ms c))
\/ m_halted (cfg_model c) <> None.

End WithSegs.

Definition overlay_argc_bytes (sp : word) (argc : nat)
(base_mem : word -> option byte) : word -> option byte :=
let bytes := word_le8 (nat_to_word argc) in
fun addr =>
if (bv_unsigned addr =? bv_unsigned sp)%Z then nth_error bytes 0
else if (bv_unsigned addr =? bv_unsigned sp + 1)%Z then nth_error bytes 1
else if (bv_unsigned addr =? bv_unsigned sp + 2)%Z then nth_error bytes 2
else if (bv_unsigned addr =? bv_unsigned sp + 3)%Z then nth_error bytes 3
else if (bv_unsigned addr =? bv_unsigned sp + 4)%Z then nth_error bytes 4
else if (bv_unsigned addr =? bv_unsigned sp + 5)%Z then nth_error bytes 5
else if (bv_unsigned addr =? bv_unsigned sp + 6)%Z then nth_error bytes 6
else if (bv_unsigned addr =? bv_unsigned sp + 7)%Z then nth_error bytes 7
else base_mem addr.

Definition enum_state (segs : list Segment) (init_pc : N) (ph : PhdrInfo)
(init_sp : word) (init_rnd : EntryDraw) (argc : nat)
(base : word -> option byte) (uid : word)
(hw : word) : machine_state :=
{| ms_regs       := ms_regs (init_machine_state segs init_pc ph init_sp init_rnd nil nil uid hw); ms_fregs := ms_fregs (init_machine_state segs init_pc ph init_sp init_rnd nil nil uid hw);
ms_pc_val     := ms_pc_val (init_machine_state segs init_pc ph init_sp init_rnd nil nil uid hw);
ms_svc_pending := ms_svc_pending (init_machine_state segs init_pc ph init_sp init_rnd nil nil uid hw);
ms_resv       := ms_resv (init_machine_state segs init_pc ph init_sp init_rnd nil nil uid hw); ms_fcsr := ms_fcsr (init_machine_state segs init_pc ph init_sp init_rnd nil nil uid hw);
ms_mem        := overlay_argc_bytes init_sp argc base;
ms_rom        := ms_rom (init_machine_state segs init_pc ph init_sp init_rnd nil nil uid hw) |}.
