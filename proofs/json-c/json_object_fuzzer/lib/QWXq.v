(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)

From OssFuzzTheorems.Proofs.Shared Require PlacementSearch.
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import ListNotations.

Definition byte_ok (s : PrimString.string) (off : N) : bool :=
match hex_byte_at s off with Some _ => true | None => false end.

Fixpoint scanN (s : PrimString.string) (fuel : nat) (base n : N) : bool :=
match fuel with
| O => N.eqb n 0
| S f =>
if N.eqb n 0 then true
else if N.eqb n 1 then byte_ok s base
else let h := N.div2 n in (scanN s f base h && scanN s f (base + h) (n - h))%bool
end.

Lemma scanN_sound : forall s fuel base n,
scanN s fuel base n = true -> forall i, (i < n)%N -> hex_byte_at s (base + i)%N <> None.
Proof.
intros s fuel. induction fuel as [|f IH]; intros base n H i Hi; cbn [scanN] in H.
- apply N.eqb_eq in H. lia.
- destruct (N.eqb_spec n 0) as [E0|Hn0]; [lia|].
destruct (N.eqb_spec n 1) as [E1|Hn1].
+ subst n. replace i with 0%N by lia. rewrite N.add_0_r. unfold byte_ok in H.
destruct (hex_byte_at s base); [discriminate|discriminate].
+ apply andb_prop in H as [H1 H2].
rewrite N.div2_div in *.
set (h := (n / 2)%N) in *.
destruct (N.lt_ge_cases i h) as [Hl|Hge].
* exact (IH _ _ H1 i Hl).
* specialize (IH _ _ H2 (i - h)%N ltac:(lia)).
replace (base + h + (i - h))%N with (base + i)%N in IH by lia. exact IH.
Qed.

Lemma segment_byte_at_some1 : forall s (n : N) (off : N),
scanN s 64 0 n = true ->
(n <= Z.to_N (Uint63.to_Z (PrimString.length s) / 2))%N ->
(Z.of_N off < Z.of_N n)%Z ->
segment_byte_at [s] off <> None.
Proof.
intros s n off Hs Hn Hoff. cbn [segment_byte_at].
replace (off <? Z.to_N (Uint63.to_Z (PrimString.length s) / 2))%N with true
by (symmetry; apply N.ltb_lt; lia).
exact (scanN_sound s 64 0 n Hs off ltac:(lia)).
Qed.
End Mq0.
From LinuxProcessSemantics.LinuxProcessSem Require State.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.


From LinuxProcessSemantics.LinuxProcessSem Require StackLayout Fs Monad Specs Run OmniRun.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence OmniEquivalence.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.Lists.List Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.LinuxProcessSem.OmniRun.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence LinuxProcessSemantics.EquivalenceDefinition.OmniEquivalence.

Import ListNotations.

Ltac norm_fd32 :=
repeat match goal with
| |- context [fd32 AT_FDCWD] =>
change (fd32 AT_FDCWD) with AT_FDCWD32
| H : context [fd32 AT_FDCWD] |- _ =>
change (fd32 AT_FDCWD) with AT_FDCWD32 in H
| |- context [fd32 ?x] => change (fd32 x) with x
| H : context [fd32 ?x] |- _ => change (fd32 x) with x in H
end.

Ltac fd32_ok :=
solve [ reflexivity
| assumption
| apply fd32_lt31; assumption
| apply fd32_id; assumption
| apply fd32_lt31; lia
| apply fd32_id; lia ].

End Mq2.

From Stdlib Require Import ZArith Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import Specs.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uaccess.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

