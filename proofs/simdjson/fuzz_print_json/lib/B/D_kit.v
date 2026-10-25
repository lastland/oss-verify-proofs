(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import PropExec MState Mem Frame Cells Step Arr ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.A Require Export D_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.B Require Import RT_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma agree_of_pres : forall live frames sp m m' (P : Z -> Prop),
  rt_pres live frames sp m m' -> (forall x, P x -> aclient live frames sp x) -> agree_on P m m'.
Proof. intros live frames sp m m' P H HP a Ha. exact (H a (HP _ Ha)). Qed.

Lemma agree_of_pres_fp : forall live frames sp W m m' (P : Z -> Prop),
  rt_pres_fp live frames sp W m m' -> (forall x, P x -> aclient live frames sp x /\ outside W x) -> agree_on P m m'.
Proof. intros live frames sp W m m' P H HP a Ha. destruct (HP _ Ha) as [H1 H2]. exact (H a H1 H2). Qed.

Lemma agree_of_pres_ex : forall live frames sp d n m m' (P : Z -> Prop),
  rt_pres_ex live frames sp d n m m' -> (forall x, P x -> aclient live frames sp x /\ ~ (d <= x < d + n)) -> agree_on P m m'.
Proof. intros live frames sp d n m m' P H HP a Ha. destruct (HP _ Ha) as [H1 H2]. exact (H a H1 H2). Qed.
