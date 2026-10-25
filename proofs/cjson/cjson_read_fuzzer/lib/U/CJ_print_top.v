(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require Bool.
From Stdlib Require List.
From Stdlib Require Lia.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From OssFuzzTheorems.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Prelim.
From OssFuzzTheorems.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require SoftFloat.
From OssFuzzTheorems.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require FmtFp.
From OssFuzzTheorems.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require FloatScan.
From OssFuzzTheorems.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require NumFacts.
From OssFuzzTheorems.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require FloatScan_nn.
From OssFuzzTheorems.Proofs.cjson.cjson_read_fuzzer.lib.P Require NumFactsG.
From OssFuzzTheorems.Proofs.cjson.cjson_read_fuzzer.lib.U Require F_printf_iface.
From OssFuzzTheorems.Proofs.cjson.cjson_read_fuzzer.lib.U Require NumFacts_iface.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List.
From OssFuzzTheorems.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Ceil.
From OssFuzzTheorems.Proofs.cjson.cjson_read_fuzzer.lib.U Require Import CJ_iface CJ_print_iface CJ_pv_cases CJ_pv_objB CJ_pv_num.
From OssFuzzTheorems.Proofs.cjson.cjson_read_fuzzer.lib.U Require CJ_pv_objB.
Import OssFuzzTheorems.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_pv_objB.CJ_pvalue.
From OssFuzzTheorems.Proofs.cjson.cjson_read_fuzzer.lib.U Require CJ_pv_objB.
Import OssFuzzTheorems.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_pv_objB.CJ_print.
From OssFuzzTheorems.Proofs.cjson.cjson_read_fuzzer.lib.U Require Import NumFacts_iface.
From OssFuzzTheorems.Proofs.cjson.cjson_read_fuzzer.lib.U Require F_printf_iface Scan_iface F_vsnprintf F_sscanf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.


(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.


(* [comment removed for export] *)
Theorem pv_obj_case' : forall HI n, pv_case_at PV_OBJ_ENTRY HI n.
Proof. intros HI n. exact (pv_obj_case HI F_vsnprintf.sprintf_u04x_proof n). Qed.

Theorem pv_num_case' : forall HI n, pv_case_at PV_NUM_ENTRY HI n.
Proof.
  intros HI n.
  exact (pv_num_case HI F_vsnprintf.sprintf_d_proof F_vsnprintf.sprintf_g_proof F_sscanf.rsscanf_lg_proof
           NumFactsG.fmt_g_ret_proof NumFactsG.fmt_g_len25_proof NumFactsG.num_fmt_g_facts_proof
           NumFacts.fmt_g_total NumFacts.fmt_d_spec FloatScan_nn.FloatScan_junk.sscanf_junk n).
Qed.

Theorem pvalue_spec' : forall HI n, pvalue_spec_at HI n.
Proof. intros HI n. exact (pvalue_spec HI F_vsnprintf.sprintf_u04x_proof (pv_obj_case' HI) (pv_num_case' HI) n). Qed.

Theorem print_spec' : forall HI, print_stmt HI.
Proof. intros HI. exact (print_spec HI F_vsnprintf.sprintf_u04x_proof (pv_obj_case' HI) (pv_num_case' HI)). Qed.

Theorem cjprint_spec' : forall HI, cjprint_stmt HI.
Proof. intros HI. exact (cjprint_spec HI F_vsnprintf.sprintf_u04x_proof (pv_obj_case' HI) (pv_num_case' HI)). Qed.

Theorem cjprintu_spec' : forall HI, cjprintu_stmt HI.
Proof. intros HI. exact (cjprintu_spec HI F_vsnprintf.sprintf_u04x_proof (pv_obj_case' HI) (pv_num_case' HI)). Qed.

Theorem pbuffered_spec' : forall HI, pbuffered_stmt HI.
Proof. intros HI. exact (pbuffered_spec HI F_vsnprintf.sprintf_u04x_proof (pv_obj_case' HI) (pv_num_case' HI)). Qed.


End CeilWrap.
