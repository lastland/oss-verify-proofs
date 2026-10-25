(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OssFuzzTheorems.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State StackLayout Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Syscall Uapi.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OssFuzzTheorems.Proofs.Shared Require Import PlacementSearch.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition alloc_ceiling : Z := 0x7fff7f800000.
Lemma alloc_ceiling_val : alloc_ceiling = 0x7fff7f800000.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition bottomup_floor : Z := 0x2aaaaaaab000.
Lemma bottomup_floor_val : bottomup_floor = 0x2aaaaaaab000.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition init_sp_ok (h : VmMaps) : Prop := sp_window_lo <= bv_unsigned (vm_init_sp h).

Lemma alloc_ceiling_le_alloc_top : forall h, init_sp_ok h -> alloc_ceiling <= alloc_top h.
Proof. intros h H. unfold init_sp_ok, sp_window_lo in H. unfold alloc_top, alloc_ceiling, stack_max_size. lia. Qed.

Lemma alloc_top_ge_of_ceiling : forall h z, init_sp_ok h -> z <= alloc_ceiling -> z <= alloc_top h.
Proof. intros h z H Hz. pose proof (alloc_ceiling_le_alloc_top h H). lia. Qed.

Lemma init_sp_ok_init_model : forall reserved brk0 mbase sp lim inp,
  valid_sp sp -> init_sp_ok (m_vmmaps (init_model reserved brk0 mbase sp lim inp)).
Proof. intros reserved brk0 mbase sp lim inp (Hlo & _ & _). unfold init_sp_ok. cbn. exact Hlo. Qed.

(* [comment removed for export] *)
Lemma init_sp_ok_same : forall h h', vm_init_sp h' = vm_init_sp h -> init_sp_ok h -> init_sp_ok h'.
Proof. ltac2:(KReplay.run [|constr:(@LinuxProcessSemantics.LinuxProcessSem.State.VmMaps); constr:(@Corelib.Init.Logic.eq); constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.vm_init_sp); constr:(@OssFuzzTheorems.Proofs.boost_beast.http_request.lib.As.AsanCeil.init_sp_ok); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.sp_window_lo); constr:(@stdpp.bitvector.definitions.bv_unsigned)|] [|@b; @H; @E; @h'; @h|] "##:#'#3###$#%#*#/#-#,#+#1#&#5#3#4#2#.#0%#1$#2$#G##########UH#UI#$C$DWJ%$#UKE$LVM)CVNO#j#$*#$EZP,'$C#Dm##)j#%*#j#&,#j#'F#j#(F##"). Qed.

Lemma init_sp_ok_mkVmMapsFull : forall h r m na sb b l mb,
  init_sp_ok h -> init_sp_ok (mkVmMapsFull r m na sb b l mb (vm_init_sp h)).
Proof. intros. unfold init_sp_ok in *. cbn. assumption. Qed.
Scheme kc__1 := Elimination for Corelib.Init.Logic.and Sort Prop.

(* [comment removed for export] *)


(* [comment removed for export] *)
Lemma mmap_off_aligned_b_0 : mmap_off_aligned_b (Z_to_bv 64 0) = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma mmap_anon_b_of_core : forall flags c,
  mmap_flags_core flags = c -> Z.testbit c 5 = true -> mmap_anon_b flags = true.
Proof.
  intros flags c Hc Hb. unfold mmap_anon_b. apply negb_true_iff. apply Z.eqb_neq. intro H0.
  unfold mmap_flags_core in Hc.
  pose proof (Z.land_spec (bv_unsigned flags) MAP_ANONYMOUS 5) as HL. rewrite H0, Z.bits_0 in HL.
  pose proof (Z.ldiff_spec (bv_unsigned flags) MAP_NORESERVE 5) as HD. rewrite Hc, Hb in HD.
  change (Z.testbit MAP_ANONYMOUS 5) with true in HL. change (Z.testbit MAP_NORESERVE 5) with false in HD.
  destruct (Z.testbit (bv_unsigned flags) 5); discriminate.
Qed.

(* [comment removed for export] *)

Lemma page_round_up_Z_pos' : forall z, 0 < z -> 0 < page_round_up_Z z.
Proof. intros z Hz. pose proof (page_round_up_Z_ge z). lia. Qed.
Scheme kc__2 := Elimination for Corelib.Init.Datatypes.nat Sort Prop.

(* [comment removed for export] *)
Lemma firstn1_skipn_nth : forall (l : list byte) (i : nat) (d : byte),
  (i < length l)%nat -> firstn 1 (skipn i l) = [nth i l d].
Proof.
  ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Datatypes.list_ind); constr:(@Corelib.Init.Datatypes.nat); constr:(@Corelib.Init.Peano.lt); constr:(@Corelib.Init.Datatypes.length); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Lists.ListDef.firstn); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Corelib.Lists.ListDef.skipn); constr:(@Corelib.Init.Datatypes.cons); constr:(@Corelib.Lists.ListDef.nth); constr:(@Corelib.Init.Datatypes.nil); constr:(@Stdlib.micromega.ZifyClasses.rew_iff); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Stdlib.ZArith.BinInt.Z.of_nat); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Stdlib.micromega.ZifyClasses.mkrel); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Stdlib.ZArith.Znat.Nat2Z.inj_lt); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Stdlib.ZArith.Znat.Nat2Z.is_nonneg); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Corelib.Init.Datatypes.tt); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Stdlib.micromega.Tauto.X); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@kc__2); constr:(@Stdlib.micromega.ZifyClasses.rew_iff_rev); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Stdlib.micromega.ZifyClasses.mkapp); constr:(@Stdlib.ZArith.Znat.Nat2Z.inj_succ); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.EnvRing.PEadd)|] [|@d; @i; @l; @__ff; @__varmap; @__wit; @__x1; @__p1; @__arith; @cstr; @Hi0; @Hi; @n; @x; @__x2; @cstr0; @IH|] "#%)#/#j#H#$#S#%#8###F#&#T#E#R#>#(#'#)#9#D#Z#6#I#\#*#=#2#B#C#M#N#W#Y#`#a#/#h#i#l#4#3#O#Q#X#[#]#^#b#c#_#g#,#k#j#.#e#+#d#7#@#:#;#J#?#<#A#L#V#U#f#5#G#K#P6#[&#\%#2%#9$#,$#]&#3%#^%#_&#`&#a'#b%#c'#d*#e%#f$#g/#h$#i+2S%2#2#US7#US8#US*#$$F%D#&N+'FJ,($#-)FJDUS+*#+$#(+&#k##*#k#$.#k#%G#j#&/#$1)%D#%FN'F)#I*C$*CI3GCRLS#S&F&$NI#XS,(&#H4J'J.I#US+S-US*S-VS.CDUS9CUS:CVS/CIVS0CS%/C$S;#0&MEEK#S$US<E/C&S''0)MEEK#S$ZS=*MEEKJ5+MEEK$&#5,MEEK('#VS>-K*S1S2VS?HF(S1#S2m$%#WS@CIDXSAHF$#l#'*)#l#(76#l#):9#j#*C#j#+S3#.IH)DIk###Jk##%#k#*C#k#+S3#+s#>Os#6,s#?s#;#-s#@Os#8P#s#A#s#9(s#A%#'OXH$#DFl#,0*#l#-s#.s#,#l#.s#0s#4#j#/s#8#j#$s#I#j#%G##s#KPJ$s#L#%D#$s#NO&#%H##s#QS(Q+s#RD#,s#Ss#O#-s#TD%J#s#U#s#M(s#U%#k#/)#j#0G#$s#YP&#%N##s#\Qs#T*s#\##s#^QO+s#_N#,s#`s#\#-s#aN%F#s#b#s#Z(s#b%#m#)#j#/,#&H$s#gQ&#%%#$s#jS(%D#'D'%)$#*C%*C%3GCRLS#S&D'$)&#&D&+%$#USBS%1,#1,$)$#1H&j#1C#U#1`S4GGCCS)LL$S5D2/U%2`S4GGCCS)LL&S56303GCRLS#S&/&%.$#XS,.*#H4F.Is#p$s$'SC4#'$.I#VS.CFUSDCXSEC$D#VS/C7WS6Cs#j#VS0Cs$4WS6C#%/C%S'#0s#pMEEK#S$/Cs#oS'&0s#rMEEK#S$5s#sMEEK%s#n#l#'#s#is#cl#(-s#v#l#)s#zs#y#j#*C#j#2C#1Ds#%)B#)DFk##$#k#*C#k#2C#$s$BSF'#WH#s#_Jl#,,&#l#3@>#l#-s#$s###l#.s#&s#.#XSGs#<s#9s#6#WQDP##s$KSHS(+s$Ls#8#,s$Ms$I#-s$Ns#:%P#s$O#s$G(s$O%#m#)#j#/s#G#j#%G#U#Hj#0G#XSIs#\s#O#FU#Hj#/s#i#j#$s$Y#j#%G#j#4s$N#j#&s$[#j#1s$]#YSJs$^s$Ps#r#Hj#&s$^##"). Qed.
