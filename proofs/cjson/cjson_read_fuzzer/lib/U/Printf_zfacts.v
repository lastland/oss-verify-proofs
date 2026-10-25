(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool.
From OssFuzzTheorems.Proofs.cjson.cjson_read_fuzzer.lib.P Require Export Printf_zfacts.
Open Scope Z_scope.

(* The parser facts are shared; conversion targets belong to this image. *)
Definition conv_target (t : Z) : Z :=
  if t =? 115 then 0x1957c
  else if (t =? 100) || (t =? 105) then 0x19534
  else if t =? 117 then 0x1966c
  else if (t =? 120) || (t =? 88) then 0x196e4
  else 0x194e4.
