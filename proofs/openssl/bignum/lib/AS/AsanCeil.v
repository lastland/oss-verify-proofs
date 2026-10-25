(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State StackLayout Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Syscall Uapi.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OssFuzzTheorems.Proofs.Shared Require Import PlacementSearch.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition alloc_ceiling : Z := 0x7fff7f800000.

Definition bottomup_floor : Z := 0x2aaaaaaab000.

Definition placement_ok (h : VmMaps) (aZ nZ : Z) : Prop :=
  bottomup_floor <= aZ
  \/ no_higher_fit (vm_reserved h ++ vm_maps h) aZ nZ (bv_unsigned (vm_mmap_base h)).

Definition placement_ok_b (h : VmMaps) (aZ nZ : Z) : bool :=
  (bottomup_floor <=? aZ)%Z
  || negb (higher_fit_b (vm_reserved h ++ vm_maps h) aZ nZ (bv_unsigned (vm_mmap_base h))).

Definition hint_placement_ok_b (addr : word) (h : VmMaps) (aZ nZ : Z) : bool :=
  if w_is0 addr then placement_ok_b h aZ nZ else true.

Definition placement_policy : Prop :=
  forall (h : VmMaps) (a : word) (nZ : Z),
    0 < nZ -> nZ mod page_size = 0 ->
    bv_unsigned a mod page_size = 0 -> 0 < bv_unsigned a ->
    bv_unsigned a + nZ <= alloc_top h ->
    region_free (vm_reserved h ++ vm_maps h) a (Z_to_bv 64 nZ) = true ->
    bv_unsigned a + nZ <= alloc_ceiling /\ placement_ok_b h (bv_unsigned a) nZ = true.

Definition init_sp_ok (h : VmMaps) : Prop := sp_window_lo <= bv_unsigned (vm_init_sp h).

Lemma init_sp_ok_same : forall h h', vm_init_sp h' = vm_init_sp h -> init_sp_ok h -> init_sp_ok h'.
Proof. intros h h' E H. unfold init_sp_ok in *. rewrite E. exact H. Qed.





Definition zero_random_draw (rdraw : bv 128) : Prop := rdraw = Z_to_bv 128 0.
