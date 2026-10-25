(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import NArith List ZArith Lia Bool.
Require OssFuzzTheorems.cjson.cjson_read_fuzzer.images.Plain.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.cjson.cjson_read_fuzzer.lib Require Import Amb ShapeAlg ShapeSpec
  PStartup PStartupRT RealizesEqv TopUbsan.
From OssFuzzTheorems.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require MState PropExec Frame.
From OssFuzzTheorems.Proofs.cjson.cjson_read_fuzzer.lib.P Require DrvTop.
From OssFuzzTheorems.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require KInv2.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Notation psegs := OssFuzzTheorems.cjson.cjson_read_fuzzer.images.Plain.M.loaded_segments (only parsing).
Local Notation ppc := OssFuzzTheorems.cjson.cjson_read_fuzzer.images.Plain.M.init_pc (only parsing).
Local Notation pph := OssFuzzTheorems.cjson.cjson_read_fuzzer.images.Plain.M.phdrs (only parsing).

(* The sanitizer proofs need the plain realization at their source budget. *)
Theorem plain_realizes04_lim : forall (lim : Z), (OssFuzzTheorems.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KInv2.drv_limit <= lim)%Z ->
  forall (sp brk mbase : word) (rnd : EntryDraw) (inp : ProcInput),
  valid_entry SRC0 (mkEntry sp brk mbase rnd) inp -> valid_input inp ->
  realizes psegs (init_config psegs ppc pph sp brk mbase rnd lim inp) (spec04 (in_argv inp) (in_fs inp)).
Proof.
  intros lim Hlim sp brk mbase rnd inp Hen Hinp.
  pose proof (valid_input_va_size _ Hinp) as Hsv48.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hen.
  destruct Hen as [Hsp [Hbrk [Hmb Hfit]]].
  pose proof Hinp as Hinp'. destruct Hinp as [Hargv [Henvp _]].
  apply (p_startup_rt sp brk mbase rnd lim inp _ Hsp Hbrk Hargv Henvp).
  intros tid regs mem Htid ME.
  assert (E : (0x1214c : word) = Z_to_bv 64 0x1214c) by (apply bv_eq; reflexivity).
  rewrite E. exact (OssFuzzTheorems.Proofs.cjson.cjson_read_fuzzer.lib.P.DrvTop.p_main_proof_lim lim Hlim sp brk mbase rnd inp tid regs mem Hsp Hbrk Hmb Hinp' Hfit Htid ME).
Qed.

Lemma sanitizer_limit_ok : (OssFuzzTheorems.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KInv2.drv_limit <= sanitizer_source_limit)%Z.
Proof. unfold OssFuzzTheorems.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KInv2.drv_limit, sanitizer_source_limit. lia. Qed.
