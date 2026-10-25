(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Yao Li: extracted the shared table and proof from separate
   double-conversion proof modules in this repository. *)
From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition five_tbl : list Z := [5; 25; 125; 625; 3125; 15625; 78125; 390625; 1953125; 9765625; 48828125; 244140625].

Lemma five_tbl_nth : forall r, 1 <= r <= 12 -> nth (Z.to_nat (r - 1)) five_tbl 0 = 5 ^ r.
Proof.
  intros r Hr.
  assert (H : forallb (fun k => nth k five_tbl 0 =? 5 ^ (Z.of_nat k + 1)) (seq 0 12) = true) by (vm_compute; reflexivity).
  pose proof (proj1 (forallb_forall _ _) H (Z.to_nat (r - 1)) ltac:(apply in_seq; lia)) as H1. cbn beta in H1.
  apply Z.eqb_eq in H1. rewrite H1. f_equal. lia.
Qed.
