(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From OssFuzzTheorems.Proofs.Shared Require Export ZBits.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From OssFuzzTheorems.Proofs.Shared Require Import PlacementSearch.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.boost_json.fuzz_parse.lib.Lib Require Export LiaTuning.
Require Import OssFuzzTheorems.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OssFuzzTheorems.Proofs.boost_json.fuzz_parse.lib Require KReplay.
Ltac2 kr_t_PropExec () := KReplay.lz_vm "#%HiC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rK!sD+7Numbers7BinNums8positive02!sKG1!sK=1N02I45stdpp9bitvector;definitions2bv00!uKA3Sem5is_x0!t7,!uG-2eq!tQ?!tv,3I!se19Datatypes4bool0!t,-!u>4Z02C56Stdlib6ZArith6BinInt1Z3pow!sC<6modulo!tI,!t%60C!vA@;bv_unsigned!t6<8eqb_refl!y7I6bv_eqb!v02!vo,0!u#>N!vH/!vh81!tu<2le!sB>t!t^83and00!s]<7testbit!vc'7n!t~%1ZGbounded_iff_bits_nonneg!{~85proj!y^-!uO8!{v>1Z01!t#=!yT=4land!wN9or!um>;!s^#!uG'!sK;>pow_po!uo+!sN;:!sN#!sJB7compare!vA=list01!|t=!sF$0K4!t/&9micromega6VarMap1t02I!sD?0!sD6=RingM!s4'7Formula!t587Env!sT#5PExpr01!sIE!x^-!uC26op!}S#!sH#!sk45Tauto8G!tZ'6C!sJ<B!sJ&!sH6:Z!uL+=Z!sT$Checker!sR6!vA&4find!sqAC!sq0_s!|0#!wX@!{;3!x>-andb!vbE7!sI6!w{:1c5?OssFuzzTheorems6Proofs6Shared5ZBits>Z_!~R&_high!zp<9!|1$spec!s~IAZ_!#38&by!#37#!#9g7!#4>#!yS7!xf34!sJF3!sJF5!sJF8!w+D3Op203!zI<5eKi!#473!x[-uni!}s9!se%4ki!v4%!sf@!~{3!vo%4True!#9i-!sb2:!#4$$ison!~a8!{E-;!xq%!xK$!t|8!v265!#=p<lor!#62<lor!#62%!|O@3!|O<3orb!#=g<!t,#!zz#!#90=xor!#9i73iff!#9/=x!u/?!yo39!~^=x!u6?9!t5$!u7@3div!#9e<div_pos!x2D5Psatz!#3m7!#48&3Pol!#8=?!sG$!}A7!t983!{L<3nat!#8a7!sn8!sOL6!sO6!{[;!#:Q<!#<n$!#:OF!#;`E!|C>mul!sC<B!xD#le_upper!#6l$!zg>e_lt_trans!#H-<shift!}\=?!sF%_!yd%w!w9L5!xRA!v@7!wX;1!#IU@7bv_wrap!vo=add!siA?bv_half_!#K3#u!vL=3su!#=HE3C3!#Gq%tactics<f_equal_help!tYAC!uD&_add_idemp_l!#4R76!#Q>$!stA8bv_s!su#!#7pH!#K><8!t]#commc8!#>H9:boost_json:fuzz_parse3lib3Lib8PropExecD!t`'!uW1!u;?=!sY+!s'#!#;+;!#E$&!#Rl;?!s<2>!#O8#!sE+=ov_read_bytes!u^c3rdn!#F{C1!tyZ;memory!t}$K!#UuC!|NB6bv!wR#!ugc7seg_rom!#;5;7nat!zp#I!ujJ<MemImageType7Segmen!#L1#!#3^>!#X18!#AW$!u~B5!#U%#!sJA:!sJ#xtract!#U~H4sext!vyc4v_lw!tgA9!|2#!#X0$!#6'@Z_to_b!#>u<4of_N!#C:<!#8\%0_r!#4uD!vG&!#Yr+!sX@@!th&!sUJ>!ug&!t4#e!#5]BG!sS1!t1+!#__?!}SL6BvBase=!#3>#_le!u>#Z!#<_A!#5IAD!u~-_in_range!zYE!#:]B=!tJ%!#Ze8!|X,8lis!}a$!sH<6lengt!#PH<6of_nat!#do8iff!#_P%!#:23;ZifyClasses;rew!#\h#rev!#9ld!wb/!#ZH94Znat5Nat2Z9i!#[9&!#@6M!#P&6!uG/5mkre!ulC7!ul&!#?LD4!#D#<!xU&!#J[#!t=A3inj!u,Eapp!sKB6!sK$2!sL68!sL#Inst7Inj_Z!|$5!w=-8inj_succ!#OY<!tY#!#La;lor_0_!#Gd<!#4m$l!#4m#!sk<mu!sGA9!t4#asso!#NW<!|v'!~I&!t]Clo!#6LA@!#DC&!~i'!{vc6!#>1#i!#EaS!tvB?!#?1$!#4i'!tuc9b!su#sex!#<\A!#oH#alu64!v7gndi!u/du64!wpi<!wH#!ss+!#_mG<Z_!#`G#!#9'E=!xQ'smal!#K-<sym!#DrE!#<tB!y4$!#<l/!xB?5Instr!xD#op0:!vec5v_ori!v^I;Z!}H#!v]G5b!s}#!#@7Dor!ukW9!{3fx!ulL!yL#x!umI!x\#!#^y#!x\C!sv#!uoV6!#b/=t!#^p,N!sC+Nat1N2l!u-BE!#D51!#E>&!#x?Jlt!#O}c6v_slti!#;J73N2Z6inj_le!vKN4!u6Ou!#OLc!u6%u!toN5!}rf!#QVe5v_sub!slgl!#O7c!xt%!wSd!v7#n!v7d4v_or!tYf!~p$!#RrGz!#Rre8u6!#4Y%!#C-;mod!#:v%!#RK<ne!#MD<!#uU$!sI$!#<3@!#Qp&!#<3%!#8\Bzero!#QmK!sS-!#B5k!z=$l!#@sc;shamt6_mask!#WDE!#RUEB!sN+!#9,V3!v6grl!#;vI>Z!ty%!#;xG!uw+!#;{A!uw+!#;~W7!uwha!#J5A:bv_a!uCGC!sO,!uDW8!#7Rgl!slc=reg!{M#4!{N$!tbgr!#4?<=mod!$36#!#r8$!#ST49SatDivModCZ_!sS#!#WL$!s,&!tlha!#N&Elow32!xlAA!#a8,!#4eh8u5!|z%!$?m9x01!vP+!vw&:Znumt!t<#y<Z!vM#di!#^d#!y'd!#MN%32!stg>!vm$!#d#,!#RJF32!#CReaddiw!#_Cd!#r14!#?7c!#f^#!#rS''!suc?sext!w&-!#46M1!#GZgliw!#~wE7!#|v<mul!~O$!#v1&!#}G@l_!sV#pow!y<d!wO,cong!xFd!#>s$5!#6K#!$4;75False00!w<grl!{De!sn$a!sne<!~C%!#CHkadd!tbd6!#M&#w!#6424ZdivBZminus!z2-!$A/+!sNA!#CkA6!yg#ub!#V<Dsub!}fW!{Xd!#GE$!v{d!#>w%32!#>wg!#Er$!x`hra!smd5v_mu!#B9c6!sl$h!#>Vc!sm%s!#X'f!so#!#TFfdi!#tbc5v_rem!#>KD!#no#!t>f!wT%!$Y@<!#9x1!#IsA!~D#mu!~iB!~D#!s|#!~DPmulop!$3q=3eqb!$U}?3!tcA8bv_quot!#Uo<4!sE#!#F|D!sk$!#Tck7div0_!#C|d6!z[$w!w1N5!uaA7b!zg$!$;;=!{,$!#u6B!si#!#X0nrem!u[O7!u[Ediv!#3if!sm#!thO6!thEmod!thgrem!thP8!$Lk8n!|'CE!$Ae1_twic!#Y8A>!$-]+!$K\N4!#@B7?!#SB$p!ss#fu!#`BB9bv_conca!#c;c5v_lu!#lk3!$H?,t_ge_case!uW7!$+-1!#p4=op!$DTA!#IK+!#xG<9!#HW#_i!#h0d;!t<+h!us=!$'C%!$&V,!#r=1!$HUDB!wo+!#6tlv_auipc!xhdb!xh$!$C5X:fetch_wor!#Ur;!shB8is_ecall!$\N<prod!$rhB7DecodeC:d!s-$_any!#35Gi!s+#08!$Rx<!tK$1!$C`J!uS2>machine_resul!$Ci#!$I7Xac!s?#_report!#Q8d4mks!$-7;!tZBD!w$&exec_!tf%es!srZ6ms_m!#Dx<!v4C!z;,_ov!skZ>!sk%tail!yK#!tYafailur!#{j;!yDR2!snj3!uKZBdrop!xQ&!z9&!z7dget!#ZGc6regup!#3wZ7m!uC#g!zq[8ms_f!sf^9ms_pc_va!$|};!|BFreg!ut`s!|<[!se#fcs!#|=;!u2Gom!{>Z=!{>'stat!%,3#!#Q7B4cor!$R|#!sODexec!uKZCinterp_eff!#5fb<!|{&value!u+E6c!{0@!#T7,c!zrA!vP/_p!v#<!tH2!y\=!sO0!yF^?!vn&!$>0%!u6B!#>B&Bis_!#BZ#ed_illega!#[Vc7fp!w1$!#4icfp_!v,>!wx-reg_ge!$Z&I9!%7;#_se!$1vdb_npc!$ECc=!%2c$0_!%6[#!xlZ5!#6%#!scZ4ste!#K1A4BvWf!#4:Z!#Bp0!#4:;!#=AQ!#E?Z!#5q1!#E>;!#5q2!sOB!#i4/!sRI!#Gw$!$hx[!$f}%!v|%!zDc9alu!$=k$!spc>!yd#_opimm_gen!uTK!$^~&!$6E#le!$kF$!$TN=od_1!#o3,4Bool!s'$;orb_f!#RT#!$Tm<=!%-y&neg!sM>A!$'P$w2!%:W$l!%?I=!$Ye$!$}BAB!sv1!%0F#!u8@!#xp<!}^#s_inj!#|Dc<!$%=%8_mo!$y><!$Wt$!%%%&!tBc@!$_q'!x^&!{kZ@!#L@#!yH-".
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv3h5LinuxProcessSemantics5Riscv7Preludek15bvmap37Corelib4Init9Datatypesmf4bool37Corelib4Init5Logicoe1Ik16bv_eqb3h5LinuxProcessSemantics5Riscv3Semqf7reg_gethf2BVhf4BvWfhf7Z_to_bvk19bvmap_setoe2eqqf5is_x001Z46Stdlib6ZArith6BinInt1Zhgd6modulohgd3powhf7bv_wraphgd2lemf5falseoe3andhgd2lthgd7testbithgd4landhgd3lorhgd4lxorhgd6shiftrhgd3addhf8bv_swrap01Nhf9bv_signedhfbbv_unsignedhgd3subhgd3mulk16bv_ltsk16bv_ltu8fOssFuzzTheorems6Proofsaboost_jsonafuzz_parse3lib3Lib8PropExec7WithFP1ht56v_addiht54zsighgd3ltbht55c_ltsht55c_ltuhgd6shiftlhgd3eqbhgd4quothgd3remhgd3divmf4listmf6option3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypeine7Segmentmf4Nonemf4Some3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsiscbmemory_readmf3natiscdov_read_bytesht53rdn02N0k14sextht54v_lwhfabv_extract3h5LinuxProcessSemanticsfLinuxProcessSem6BvBasejl0dbytes_le_to_Zmf6lengthhgd6of_natmf3apphf6bv_add3h5LinuxProcessSemantics5Riscv5Instrjr27ALU_SLTqf5alu64ht56v_sltijr27ALU_ADDht55v_addjr27ALU_SUBht55v_subht55v_sltjr28ALU_SLTUht56v_sltujr27ALU_ANDht55v_andjr26ALU_ORht54v_orjr27ALU_XORht55v_xork14zexthf6bv_andjr27ALU_SLLht56v_sllijr27ALU_SRLht56v_srlijr27ALU_SRAht56v_sraiht55v_sllht55v_srlht55v_sraqf5low32qf5alu32ht57v_addiwht57v_slliwht57v_srliwht57v_sraiwht56v_addwht56v_subwht56v_sllwht56v_srlwht56v_srawjr25M_MULqf7mul_divht55v_muljr26M_MULHht56v_mulhjr28M_MULHSUht58v_mulhsujr27M_MULHUht57v_mulhujr25M_DIVht55v_divjr25M_REMht55v_remht56v_mulwht56v_divwht56v_remwjr26M_DIVUht57v_divuwjr26M_REMUht57v_remuwhfabv_modulusoe3nothffbv_half_modulusht55v_luihf9bv_concatht57v_auipcjr25instrmf4prodiscdmachine_state7fOssFuzzTheorems6Proofsaboost_jsonafuzz_parse3lib3Lib8PropExecmnc4mkstmf4pairisc9MachineOkiscafetch_wordisc8is_ecalliscemachine_resultisc4step3h5LinuxProcessSemantics5Riscv7DecodeCngbadecode_anyjr25OpImmjr25aluopmnc4getrmnc6regupdmnc6v_addimnc7v_sltiumf4trueisch3Build_machine_statemnc6fp_csrmnc7fp_regsjl0dZ_to_le_bytesisch0word_to_le_bytes" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Class FPState := mkFP { fp_regs : bvmap 5 word; fp_csr : bv 32 }.

Definition mkst `{fx : FPState} (regs : bvmap 5 word) (pc : word) (mem rom : word -> option byte) : machine_state :=
  {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
     ms_svc_pending := None; ms_resv := None; ms_fcsr := fp_csr;
     ms_mem := mem; ms_rom := rom |}.

Section WithFP1.
Context {fx : FPState}.

(* [comment removed for export] *)
Definition getr : ltac2:(zQ "30!h9!jc!m7>4regs@2$2@1$0#5@1$1@1$0#k0>1r@1$1@1$0#5@1$1@1$0#k0") := ltac2:(zQ "a0!h9!jc!o7!q2!q6!m7!t1!tb!u0!u7\4regs@2$5@1$0#5@1$1@1$0#k0\1r@1$1@1$0#5M2\0$2@1$1@1$0#k0@3$4@1$0#5^1@3$7@1$0#5ZKv$3@2$8@1$0#5Z@2$9@1$0#k0Z@2$6^2^1").
Definition regupd : ltac2:(zQ "30!h9!jc!m7>4regs@2$2@1$0#5@1$1@1$0#k0>1r@1$1@1$0#5>1v@1$1@1$0#k0@2$2@1$0#5@1$1@1$0#k0") := ltac2:(zQ "40!h9!jc!m7!v1\4regs@2$2@1$0#5@1$1@1$0#k0\1r@1$1@1$0#5\1v@1$1@1$0#k0@5$3@1$0#5@1$1@1$0#k0^2^1^3").

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma bv_eqb0_is_x0 : ltac2:(zQ "90!h9!o7!q2!vd!q6!hg2!tb!u0!jc>1r@1$8@1$0#5@3$3$1@3$4@1$0#5^1@3$6@1$0#5ZKv$2@2$7@1$0#5Z@1$5^1").
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01rp;1p;2p10000p4p7210p1000\p4p710p8g001:j15Tg001_j14Tg002Dj10Tg002bj11Tg003Ej13Tg003mj22Tg004G#5#4#0#1g004lf0#3'2W0o"). Qed.

Lemma bv_wrap32_mod : ltac2:(zQ "60!hga!vd!h9!hi5!hif!hj6>1z$0@3$1$0@2$5@1$2#i0^1@2$3^1@2$4+2+i0").
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01zp;1p;2g001:j10Tg005Lj11Tg005jj23Tg006Gj22Tg003mj24Tg006gR0f0g004G#0R1#1%01#0#0#0#1'3'2,40W0o"). Qed.

Lemma bv_eqb_refl : forall {n} (a : bv n), bv_eqb a a = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01ah11np;1p;2p;3g002bj14Tg007Ej23Tg007oj10Tg008Qj31Tg009>j32Tg009Xf0R0#4f1R1/30#0g004lA1100g00:632eW0W1o"). Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)













(* [comment removed for export] *)
Lemma bv_swrap_add_idemp_l : ltac2:(zQ "60!hga!ho6!hod!vd!hp8!hj6>1n$4>1x$0>1y$0@3$3$0@2$2^3@2$1@2$5^3^2^1@2$2^3@2$1^2^1").
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h07__arithh14__x1h24__x2h34__x3h41zh51Hh64__ffh78__varmaph85__with91nh:1xh;1yp;2p;1p;4p;3p;7p;8p;6g00fdj21j1@Tg00gJj20Tg00ggj15Tg00hUR0j18Tg003mj24Tg00B2j1ITg00BRj1CTg00C2j29Tg00VEj4>Tg00CPj1=Tg00Cnj1<Tg00E<j27Tg001:j1;Tg001_j1KTg00i2j33Tg00Jcj4JTg00N9j7HTg00Fej2GTg00GGj2DTg009>j32Tg00H3j3BTg00HRj4ATg00iUj86Tg00j2j3?Tg000\j6ETg00jdj6FTg00k@j2:Tg009Xg006gR1P1P1f2R2f1R3,12R4f0R5'0R6%52R7'0R8'1R9#81035R:/07,12R;#8P7P7P1P1\1R<P0P0P9P;P<\1/40g00T1R0#I%C0P11912P3f3R0,91C>%=1%<1R;g00Q0g00QOR9P9g00QoR9P1g004GR=,71R>%;=,71R?%K=,71R=531531g00kgA31>?=31=CJg00ROFH1G;9P5P2g004lR9g00:6R;'41D52=29;dg00=o=B13CAb6b7b8X11X21X31R;1032,051053/02521^11^21^31R9P5%50R=P31102R?O3b01057,04=218P1103=R8,0?R4f4R>/151002%5>R@'0,1>R>521X41P11028RA,10A215>X41P1P1%@0R>P>PA1023/0=14<>P;P9P5P@P2P0O3b0G61104A?028EE10?3/0=P5EFb5G61417G61:261:2:521eX;1W:W9o"). Qed.

Lemma bv_swrap_add_idemp_r : ltac2:(zQ "60!hga!ho6!hod!vd!hp8!hj6>1n$4>1x$0>1y$0@3$3$0@2$2^3@2$1^2@2$5^3^1@2$2^3@2$1^2^1").
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01zh11nh21xh31yp;2p;3p;6g00fdj27Tg00gJj21Tg00k@j20Tg009>j33Tg003mj26Tg00lNj24Tg000\j62Tg00m0j35Tg009Xg006gR0P0f2R1f0R2'7R3f1R4'1R5f3R6/021114,06R6530X00R7P01124R8,01A3026X00P01142R6P71016,60P81424E21015A5124E211431443E2X30W2W1o"). Qed.

Lemma bv_swrap_wrap' : ltac2:(zQ "50!hga!hod!vd!hp8!hj6>1n$3>1z$0@3$2$0@2$1^2@2$4^2^1@2$1^2^1").
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01nh11zp;2g00nEj20Tg009Xg006gf1f0'0W1W0o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition zsig : ltac2:(zQ "30!h9!hga!jc>1x@1$2@1$0#k0$1") := ltac2:(zQ "30!h9!jc!hpb\1x@1$1@1$0#k0@2$2@1$0#k0^1").

Definition v_addi : ltac2:(zQ "30!h9!jc!hga>1x@1$1@1$0#k0>3imm$2@1$1@1$0#k0") := ltac2:(zQ "60!h9!hga!ho6!u7!jc!hq7\1x@1$4@1$0#k0\3imm$1@2$3@1$0#k0@2$2@2$5@1$0#k0^2^1").
Definition v_add : ltac2:(zQ "20!h9!jc>1x@1$1@1$0#k0>1y@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "50!h9!jc!hq7!ho6!u7\1x@1$1@1$0#k0\1y@1$1@1$0#k0@2$4@1$0#k0@2$3@2$2@1$0#k0^2@2$2@1$0#k0^1").
Definition v_sub : ltac2:(zQ "20!h9!jc>1x@1$1@1$0#k0>1y@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "50!h9!jc!hq7!hr5!u7\1x@1$1@1$0#k0\1y@1$1@1$0#k0@2$4@1$0#k0@2$3@2$2@1$0#k0^2@2$2@1$0#k0^1").
Definition v_mul : ltac2:(zQ "20!h9!jc>1x@1$1@1$0#k0>1y@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "50!h9!jc!hq7!hrc!u7\1x@1$1@1$0#k0\1y@1$1@1$0#k0@2$4@1$0#k0@2$3@2$2@1$0#k0^2@2$2@1$0#k0^1").
Definition v_andi : ltac2:(zQ "30!h9!jc!hga>1x@1$1@1$0#k0>3imm$2@1$1@1$0#k0") := ltac2:(zQ "70!h9!hga!hm5!u7!jc!hq7!hj6\1x@1$4@1$0#k0\3imm$1@2$3@1$0#k0@2$2@2$5@1$0#k0^2@2$6@1$0#k0^1").
Definition v_ori : ltac2:(zQ "30!h9!jc!hga>1x@1$1@1$0#k0>3imm$2@1$1@1$0#k0") := ltac2:(zQ "70!h9!hga!hmd!u7!jc!hq7!hj6\1x@1$4@1$0#k0\3imm$1@2$3@1$0#k0@2$2@2$5@1$0#k0^2@2$6@1$0#k0^1").
Definition v_xori : ltac2:(zQ "30!h9!jc!hga>1x@1$1@1$0#k0>3imm$2@1$1@1$0#k0") := ltac2:(zQ "70!h9!hga!hn4!u7!jc!hq7!hj6\1x@1$4@1$0#k0\3imm$1@2$3@1$0#k0@2$2@2$5@1$0#k0^2@2$6@1$0#k0^1").
Definition v_and : ltac2:(zQ "20!h9!jc>1x@1$1@1$0#k0>1y@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "50!h9!jc!hq7!hm5!u7\1x@1$1@1$0#k0\1y@1$1@1$0#k0@2$4@1$0#k0@2$3@2$2@1$0#k0^2@2$2@1$0#k0^1").
Definition v_or : ltac2:(zQ "20!h9!jc>1x@1$1@1$0#k0>1y@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "50!h9!jc!hq7!hmd!u7\1x@1$1@1$0#k0\1y@1$1@1$0#k0@2$4@1$0#k0@2$3@2$2@1$0#k0^2@2$2@1$0#k0^1").
Definition v_xor : ltac2:(zQ "20!h9!jc>1x@1$1@1$0#k0>1y@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "50!h9!jc!hq7!hn4!u7\1x@1$1@1$0#k0\1y@1$1@1$0#k0@2$4@1$0#k0@2$3@2$2@1$0#k0^2@2$2@1$0#k0^1").

Definition c_lts : ltac2:(zQ "30!h9!jc!o7>1x@1$1@1$0#k0>1y@1$1@1$0#k0$2") := ltac2:(zQ "30!h9!jc!hs3\1x@1$1@1$0#k0\1y@1$1@1$0#k0@3$2@1$0#k0^2^1").
Definition c_ltu : ltac2:(zQ "30!h9!jc!o7>1x@1$1@1$0#k0>1y@1$1@1$0#k0$2") := ltac2:(zQ "30!h9!jc!hsc\1x@1$1@1$0#k0\1y@1$1@1$0#k0@3$2@1$0#k0^2^1").

Definition btgt : ltac2:(zQ "30!h9!jc!hga>2pc@1$1@1$0#k0>3imm$2@1$1@1$0#k0") := ltac2:(zQ "40!h9!hga!ihc!jc\2pc@1$3@1$0#k0\3imm$1@2$2^2^1").

(* [comment removed for export] *)
Definition v_slti : ltac2:(zQ "30!h9!jc!hga>1x@1$1@1$0#k0>3imm$2@1$1@1$0#k0") := ltac2:(zQ "70!h9!o7!u7!jc!hga!ii6!iie\1x@1$3@1$0#k0\3imm$4M1\0$1@1$3@1$0#k0@2$6@1$5^2^1@2$2@1$0#k0+1@2$2@1$0#k0Z").
Definition v_sltiu : ltac2:(zQ "30!h9!jc!hga>1x@1$1@1$0#k0>3imm$2@1$1@1$0#k0") := ltac2:(zQ "80!h9!o7!u7!jc!hga!iie!hq7!hj6\1x@1$3@1$0#k0\3imm$4M1\0$1@1$3@1$0#k0@2$5@2$6@1$0#k0^2@2$7@1$0#k0^1@2$2@1$0#k0+1@2$2@1$0#k0Z").
Definition v_slt : ltac2:(zQ "20!h9!jc>1x@1$1@1$0#k0>1y@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "50!h9!jc!o7!u7!ij5\1x@1$1@1$0#k0\1y@1$1@1$0#k0M2\0$2@1$1@1$0#k0@2$4^2^1@2$3@1$0#k0+1@2$3@1$0#k0Z").
Definition v_sltu : ltac2:(zQ "20!h9!jc>1x@1$1@1$0#k0>1y@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "50!h9!jc!o7!u7!ije\1x@1$1@1$0#k0\1y@1$1@1$0#k0M2\0$2@1$1@1$0#k0@2$4^2^1@2$3@1$0#k0+1@2$3@1$0#k0Z").

(* [comment removed for export] *)
Definition v_slli : ltac2:(zQ "30!h9!jc!hga>1x@1$1@1$0#k0>2sh$2@1$1@1$0#k0") := ltac2:(zQ "60!h9!hga!ik7!u7!jc!hq7\1x@1$4@1$0#k0\2sh$1@2$3@1$0#k0@2$2@2$5@1$0#k0^2^1").
Definition v_srli : ltac2:(zQ "30!h9!jc!hga>1x@1$1@1$0#k0>2sh$2@1$1@1$0#k0") := ltac2:(zQ "60!h9!hga!hnc!u7!jc!hq7\1x@1$4@1$0#k0\2sh$1@2$3@1$0#k0@2$2@2$5@1$0#k0^2^1").
Definition v_srai : ltac2:(zQ "30!h9!jc!hga>1x@1$1@1$0#k0>2sh$2@1$1@1$0#k0") := ltac2:(zQ "60!h9!hga!hnc!u7!jc!hpb\1x@1$4@1$0#k0\2sh$1@2$3@1$0#k0@2$2@2$5@1$0#k0^2^1").

(* [comment removed for export] *)
Definition v_sll : ltac2:(zQ "20!h9!jc>1x@1$1@1$0#k0>1y@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "60!h9!jc!hq7!hi5!ik7!u7\1x@1$1@1$0#k0\1y@1$1@1$0#k0@2$5@1$0#k0@2$4@2$2@1$0#k0^2@2$3@2$2@1$0#k0^1+k0").
Definition v_srl : ltac2:(zQ "20!h9!jc>1x@1$1@1$0#k0>1y@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "60!h9!jc!hq7!hi5!hnc!u7\1x@1$1@1$0#k0\1y@1$1@1$0#k0@2$5@1$0#k0@2$4@2$2@1$0#k0^2@2$3@2$2@1$0#k0^1+k0").
Definition v_sra : ltac2:(zQ "20!h9!jc>1x@1$1@1$0#k0>1y@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "70!h9!jc!hi5!hnc!u7!hpb!hq7\1x@1$1@1$0#k0\1y@1$1@1$0#k0@2$4@1$0#k0@2$3@2$5@1$0#k0^2@2$2@2$6@1$0#k0^1+k0").

(* [comment removed for export] *)
Definition v_lui : ltac2:(zQ "30!h9!hga!jc>3imm$1@1$2@1$0#k0") := ltac2:(zQ "30!h9!hga!u7\3imm$1@2$2@1$0#k0^1").
Definition v_auipc : ltac2:(zQ "30!h9!jc!hga>2pc@1$1@1$0#k0>3imm$2@1$1@1$0#k0") := ltac2:(zQ "60!h9!hga!ho6!u7!jc!hq7\2pc@1$4@1$0#k0\3imm$1@2$3@1$0#k0@2$2^1@2$5@1$0#k0^2").

(* [comment removed for export] *)
Definition v_addiw : ltac2:(zQ "30!h9!jc!hga>1x@1$1@1$0#k0>3imm$2@1$1@1$0#k0") := ltac2:(zQ "70!h9!hga!ho6!u7!jc!hod!hq7\1x@1$4@1$0#k0\3imm$1@2$3@1$0#k0@2$5@1$0#i0@2$2@2$6@1$0#k0^2^1").
Definition v_slliw : ltac2:(zQ "30!h9!jc!hga>1x@1$1@1$0#k0>2sh$2@1$1@1$0#k0") := ltac2:(zQ "70!h9!hga!ik7!u7!jc!hod!hq7\1x@1$4@1$0#k0\2sh$1@2$3@1$0#k0@2$5@1$0#i0@2$2@2$6@1$0#k0^2^1").
Definition v_srliw : ltac2:(zQ "30!h9!jc!hga>1x@1$1@1$0#k0>2sh$2@1$1@1$0#k0") := ltac2:(zQ "80!h9!hga!hnc!u7!jc!hod!hq7!hj6\1x@1$4@1$0#k0\2sh$1@2$3@1$0#k0@2$5@1$0#i0@2$2@2$7@1$0#i0@2$6@1$0#k0^2^1").
Definition v_sraiw : ltac2:(zQ "30!h9!jc!hga>1x@1$1@1$0#k0>2sh$2@1$1@1$0#k0") := ltac2:(zQ "70!h9!hod!hga!hnc!u7!jc!hq7\1x@1$5@1$0#k0\2sh$2@2$4@1$0#k0@2$1@1$0#i0@2$3@2$1@1$0#i0@2$6@1$0#k0^2^1").
Definition v_addw : ltac2:(zQ "20!h9!jc>1x@1$1@1$0#k0>1y@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "60!h9!jc!hq7!ho6!u7!hod\1x@1$1@1$0#k0\1y@1$1@1$0#k0@2$4@1$0#k0@2$5@1$0#i0@2$3@2$2@1$0#k0^2@2$2@1$0#k0^1").
Definition v_subw : ltac2:(zQ "20!h9!jc>1x@1$1@1$0#k0>1y@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "60!h9!jc!hq7!hr5!u7!hod\1x@1$1@1$0#k0\1y@1$1@1$0#k0@2$4@1$0#k0@2$5@1$0#i0@2$3@2$2@1$0#k0^2@2$2@1$0#k0^1").
Definition v_sllw : ltac2:(zQ "20!h9!jc>1x@1$1@1$0#k0>1y@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "70!h9!jc!hq7!hi5!ik7!u7!hod\1x@1$1@1$0#k0\1y@1$1@1$0#k0@2$5@1$0#k0@2$6@1$0#i0@2$4@2$2@1$0#k0^2@2$3@2$2@1$0#k0^1+i0").
Definition v_srlw : ltac2:(zQ "20!h9!jc>1x@1$1@1$0#k0>1y@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "80!h9!jc!hq7!hi5!hnc!u7!hod!hj6\1x@1$1@1$0#k0\1y@1$1@1$0#k0@2$5@1$0#k0@2$6@1$0#i0@2$4@2$7@1$0#i0@2$2@1$0#k0^2@2$3@2$2@1$0#k0^1+i0").
Definition v_sraw : ltac2:(zQ "20!h9!jc>1x@1$1@1$0#k0>1y@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "70!h9!jc!hod!hq7!hi5!hnc!u7\1x@1$1@1$0#k0\1y@1$1@1$0#k0@2$6@1$0#k0@2$2@1$0#i0@2$5@2$2@1$0#i0@2$3@1$0#k0^2@2$4@2$3@1$0#k0^1+i0").

(* [comment removed for export] *)
Definition v_mulh : ltac2:(zQ "20!h9!jc>1x@1$1@1$0#k0>1y@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "60!h9!jc!hpb!hrc!hnc!u7\1x@1$1@1$0#k0\1y@1$1@1$0#k0@2$5@1$0#k0@2$4@2$3@2$2@1$0#k0^2@2$2@1$0#k0^1+k0").
Definition v_mulhsu : ltac2:(zQ "20!h9!jc>1x@1$1@1$0#k0>1y@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "70!h9!jc!hrc!hnc!u7!hpb!hq7\1x@1$1@1$0#k0\1y@1$1@1$0#k0@2$4@1$0#k0@2$3@2$2@2$5@1$0#k0^2@2$6@1$0#k0^1+k0").
Definition v_mulhu : ltac2:(zQ "20!h9!jc>1x@1$1@1$0#k0>1y@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "60!h9!jc!hq7!hrc!hnc!u7\1x@1$1@1$0#k0\1y@1$1@1$0#k0@2$5@1$0#k0@2$4@2$3@2$2@1$0#k0^2@2$2@1$0#k0^1+k0").
Definition v_mulw : ltac2:(zQ "20!h9!jc>1x@1$1@1$0#k0>1y@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "60!h9!jc!hq7!hrc!u7!hod\1x@1$1@1$0#k0\1y@1$1@1$0#k0@2$4@1$0#k0@2$5@1$0#i0@2$3@2$2@1$0#k0^2@2$2@1$0#k0^1").

(* [comment removed for export] *)
Definition v_div : ltac2:(zQ "20!h9!jc>1x@1$1@1$0#k0>1y@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "80!h9!jc!o7!ii6!u7!il1!il8!hq7\1x@1$1@1$0#k0\1y@1$1@1$0#k0M2\0$2@1$1@1$0#k0@2$5@2$7@1$0#k0^1Z@2$4@1$0#k0-1@2$4@1$0#k0@2$6@1$3^2@1$3^1").
Definition v_rem : ltac2:(zQ "20!h9!jc>1x@1$1@1$0#k0>1y@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "80!h9!jc!o7!ii6!il1!im0!u7!hq7\1x@1$1@1$0#k0\1y@1$1@1$0#k0M2\0$2@1$1@1$0#k0@2$4@2$7@1$0#k0^1Z^2@2$6@1$0#k0@2$5@1$3^2@1$3^1").
Definition v_divw : ltac2:(zQ "20!h9!jc>1x@1$1@1$0#k0>1y@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "90!h9!jc!hod!hq7!o7!u7!il1!il8!hj6\1x@1$1@1$0#k0\1y@1$1@1$0#k0M4\0$4@1$1@1$0#k0@2$6@2$8@1$0#i0@2$3@1$0#k0^1Z@2$5@1$0#k0-1@2$5@1$0#k0@2$2@1$0#i0@2$7@2$2@1$0#i0@2$3@1$0#k0^2@2$2@1$0#i0@2$3@1$0#k0^1").
Definition v_remw : ltac2:(zQ "20!h9!jc>1x@1$1@1$0#k0>1y@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "91!h9!hod!hq7!jc!o7!u7!il1!im0!hj6&@2$1@1$0#i0@2$2@1$0#k0^2\1x@1$3@1$0#k0\1y@1$3@1$0#k0M4\0$4@1$3@1$0#k0@2$6@2$8@1$0#i0@2$2@1$0#k0^1Z@2$5@1$0#k0~0@2$5@1$0#k0@2$1@1$0#i0@2$7~0@2$1@1$0#i0@2$2@1$0#k0^1").
Definition v_divuw : ltac2:(zQ "20!h9!jc>1x@1$1@1$0#k0>1y@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "91!h9!jc!hq7!hj6!o7!u7!im7!il1!hod&@2$3@1$0#i0@2$2@1$0#k0^1\1x@1$1@1$0#k0\1y@1$1@1$0#k0M4\0$4@1$1@1$0#k0@2$7~0Z@2$5@1$0#k0-1@2$5@1$0#k0@2$8@1$0#i0@2$6@2$3@1$0#i0@2$2@1$0#k0^2~0").
Definition v_remuw : ltac2:(zQ "20!h9!jc>1x@1$1@1$0#k0>1y@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "91!h9!hq7!jc!hj6!o7!u7!hod!il1!hi5&@2$3@1$0#i0@2$1@1$0#k0^1\1x@1$2@1$0#k0\1y@1$2@1$0#k0M4\0$4@1$2@1$0#k0@2$7~0Z@2$5@1$0#k0@2$6@1$0#i0@2$1@1$0#k0^2@2$5@1$0#k0@2$6@1$0#i0@2$8@2$3@1$0#i0@2$1@1$0#k0^2~0").

(* [comment removed for export] *)
Definition v_lw : ltac2:(zQ "20!h9!jc>1v@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "50!h9!u7!jc!hod!hq7\1v@1$2@1$0#k0@2$1@1$0#k0@2$3@1$0#i0@2$4@1$0#k0^1").

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition seg_rom : ltac2:(zQ "50!h9!jc!ime!in5!ir3>4segs@1$2$4>0@1$1@1$0#k0@1$3@1$1@1$0#8") := ltac2:(zQ "80!h9!jc!ime!in5!ire!is5!ir3!jg3\4segs@1$2$6\4addr@1$1@1$0#k0M3\1x@1$3@1$2@1$1@1$0#8@1$3@1$1@1$0#8@3$7^2^1@1$0#1\1l@1$2@1$1@1$0#8M2\1l@1$2@1$1@1$0#8@1$3@1$1@1$0#8^1@1$4@1$1@1$0#8\1b@1$1@1$0#8\2l0@1$2@1$1@1$0#8@2$5@1$1@1$0#8^2@1$4@1$1@1$0#8").

Fixpoint rdn (segs : list Segment) (mem : word -> option byte) (a : word) (n : nat) : option (list byte) :=
  match n with
  | O => Some []
  | S n' =>
    match (match mem a with Some b => Some b | None => seg_rom segs a end) with
    | Some b => match rdn segs mem (a+1) n' with Some rest => Some (b :: rest) | None => None end
    | None => None
    end
  end.

(* [comment removed for export] *)
Lemma ov_rdn : ltac2:(zQ "90!h9!jc!ime!in5!jh2!vd!ir3!jh8!ji9>4segs@1$2$6>3mem>0@1$1@1$0#k0@1$3@1$1@1$0#8>1n$4>1a@1$1@1$0#k0@3$5@1$3@1$2@1$1@1$0#8@4$7^4^3^1^2@4$8^4^3^1^2").
Proof.
ltac2:(KReplay.run1z (kr_t_PropExec ()) ["WithFP1"] "##9}p'0h01oi001oh11ah21bi011bh31nh42IHh51li021lh63memh72n'h84resti03!s-$h94segsi042l0i051xp;1p;4p;3p;2p;6g00BRR0j1<Tg001:j14!s/#2Dj18!s/$bj1:!s/#o1R1j1>!s1$Sj42Tg010Xj40!s8#9>j31!s/#3mj26!sA#1\j25!s/#2>j37!sA#E_j1;!s/#5Lj1?!sA#3Aj3C!s/$dj33!sA#`Rj39!s/#0\j6=!sA#4Ij2B!s8#^5j1A!s8#5Qj4@!s/#62#<g004GR2#4!s$#R3!s-%#8R4#:R5%83#:R3#>R6[g0171R7%<3R8#>R9f4R:f3R;f0R<f1R=C2P:P;P<P=C031^15R>X37P;f2R?P!t5#eYC0,69X15P:P<O1R@P6P1P3!s&$9!s+$6P<153<RAP1P8P6f7RB%82RC77?P0!sF%%;3RD153=n10110200!s&#20!s4$4REPD!s?%5!s?#10!sH$!s82100RF!t0$9f8RGPB%?2!uT#P5C4R2934;RHf5RIC2RJA93=<,58RK%;8RL!sp2300P!s:3100!uH&!t2&PGPBPHPIC0RBPK!sV43!t\$!sl6519P<P9PB!sm&<A93?!tZ$B!sk7!uG&9RMPGA34:2RNf6ROC0RPP!sW8519X09169FPJP:PHO1E=X23!wa#A7O=C!wZ$8!wd+8!wD#P!v~8RH!tq&MPGPNPOC2!u^9!vJ>!sh'P!s`M!v>%!y,#!si%E!ux&;R0f:RPA34O2RHPG!t\V!sq&P0PPP!sh#0!tdR169LRHP9f=RNf<RJA34G2RGPPC!z8+!x=$;!x=$Q!x=>>PNA34M2P0C0P!sO8!x5%!s{&F!xY9,69PNPJP!tP#2!wl#!xZ$88!x]#=P<O2!|['!x=$21!s4%X58!x{#PH!sD%0!sD#1!}&%b!|b&!s:+101b!v\'!~$%@P!}|&A7I<C!yO9!wG8!u>#OPIA34=2R2P;!x-V!tP+1BI<!t3?P!t-#!xLQePIP:P<%A?R?C2!s3%P?C!sA$X15X4>X77P<C@W3W6W9o"). Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma b_lw_val : ltac2:(zQ "70!h9!jc!vd!jj0!jj4!jjb!jk3>1v@1$1@1$0#k0@3$2@1$1@1$0#k0@3$4@1$0#i0@1$0#k0@4$6@1$0#k0$3@1$0#i0^1@1$5^1").
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01zh12b1h22b2h31nh41Hh51vp;1p;3p;2p;4p;6p;8g001:j13Tg002Dj1;Tg002bj12Tg009>j35Tg007Ej20Tg017lj3CTg018Pj49Tg0199j3>Tg019dj1=Tg01:ij28Tg00fdj24j1ITg00k@j27Tg01;Qj2<Tg003mj2HTg01<7j1GTg00cgj2:Tg00nEj2FTg01<Uj1BTg000\j66Tg01=9j4ATg00iUj8@Tg01=kj2?Tg01>Zj3DTg01?Gj3ETg006gR0f1R1f0R235p=1g004G#3#3#3#3#3R3#3#;R4#2g009XR5%22R6%21R7g00;Nf2R8#2?512f3R9/081091'1R:[10811082'1%29?581[R;f4#2?598\:AC812P2n2001000000120000000W2W1W3P;^27^16^35P2P4%;3R3P4g01@=R5P3P1C9R67>4R7%=1R;P01836R:,441048,73R9,<4,04,12X00P01041R<,73R=,44P4P5P3P8C9,83,44/12X00P0P0%I4R8P8P:P=P0\0/H8P0%G5,:<,431732/19X00P0P<1432,73/19X001F3<g00=o,:<%B<E61036P4P5P3P1CAE611:=eG@1<4=,041?4=E6AD346,04AE346E61047104;'1eO4b4W5o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma bytes_le_to_Z_nonneg : ltac2:(zQ "50!ime!h9!jnf!hk0!jc>2bs@1$0@1$4@1$1#8@2$3Z@1$2^1").
Proof.
ltac2:(KReplay.run1z (kr_t_PropExec ()) ["WithFP1"] "##2jh01ah11Hh21bh32bsh47__arithh54__ffh64__p1h78__varmaph85__with94__x1h:1nh;2IHp;1p;2p;4p;3p;6p;7p;8p;5g001:j15Tg002Dj1W!s/$bj1E!s/#BRj1:Tg01@[j11!s8$2j19!s/#IDj1D!s/#CPj1B!s/$nj1A!s/#DYj2@!s/#Jcj4;!s/#Fej2V!s/#3mj2U!s/#GGj2T!s/#9>j3O!s/#H3j3N!s/$Rj4K!s/#:Vj28!s/#UDj24!s/#;NR0j22!s:$aj2C!s/#7Ej26!s/#5Lj1F!t{#AXj23!s/#B8j2G!s/$kj1H!sg$2j27!t{$2j2I!s/#E<j2J!s/#N]j6?!s/#OAj7L!sA$_j1M!s8$ej8>!sn#CTj2P!s8#M^j4Q!s/#`Rj3=!sA#D;j5R!sn$9j7S!s/#=oR1f0R2'8p=0f1R3g00Q0R4!s,#OR5P!wB#QoR6P2g00ROFSp=<g004GR7#5!s$#R8#WR9#ER:#:R;P:%12#0R<X3;g00T1R=#9R>%:=R=g006gR?#D%B?R@%A?RAP?1@?1RBg00PIRCPBC;'<1VA6RDP2f2RE!t9#lRF!w-#6RG'U1T2E=OFGdAN?13CKRGb5b7b81811P2b4%9:#1#0eP01432#0%0ER1%03RF'2RH[%02RI,2F14E3#0[RJf3RK/4E#0\H1C32P2n20010!s#$12!s-%0X2?X0?PJ^2?^0?P2169KRJ%1E%F8R8'3RH%0JRL%0H1G9K%H9RH,7J,2Lp-0RLP>P=1I?3P@PAP4P5P5P6!s0-?PBPC1J?7C;,<AR7!sA-KE?FL%M5P7G>PDP!ua&X9?W612I3PF[^9?^6LP2f5,69R9/7HP9P3O3b4b1P013!uy#P1[13!ue#\FRF13K!uc#11P!uc<:!uc$F^:!uc%%1KP8PEO3b1CQ!s+#A=:E3!w'$X;!xU#X2:P2DRW3o"). Qed.

Lemma bytes_le_to_Z_bound : ltac2:(zQ "90!h9!jc!jp0!ime!jnf!hl4!hrc!jp9!hif>2bs@1$3@1$1@1$0#8@2$5@1$4^1@2$8+2@2$6+8@1$7@2$2@1$1@1$0#8^1").
Proof.
ltac2:(KReplay.run1z (kr_t_PropExec ()) ["WithFP1"] "##Tfh06__sat1h14__x1h22Hah37__arithh44__ffh5!sL%0h68__varmaph75__with84cstrh9!sf#2h:3Hk0h;1bh<1xh=1ah>1nh?2bsh@2H0hA4__p1hB!sw%3hC1mhD1yhE1HhF2HbhG2HkhH2IHhI!sJ%2hJ1kp&0p;1p;2p;3p;4p;6p;<p;5p;Bp;7p;8g001:j1<Tg002Dk10@!s0$bk100!s0#BRj1\Tg01@[j17!s8#5Lj1K!s8#D]j24!s8$jR0j22!s1#;2R1j26!sE#E=R2j18!s<#b9R3j21!s<$]j1k!s:#3mj2H!s/#@Ej2?!s/$mj3A!s/#AQj2y!tK$2j1^!s/#IDj1w!s/#CPj1v!s/$nj1u!s/#DYj2E!s/#J@j3]!s/#Fej2p!s/#GGj2o!s/#9>j3[!s/#H3j3n!s/$Rj4m!t^#F;j4Z!s/$fj1l!s/#B8k20!t_$7Ej2B!s9$kk10>!uV$NR4j2!vB$^5R5j1G!sF#AXj2!sE$UDj2F!s/#gJj2C!s/#:VR6j2:!sL#H;j1L!s`$Tj2W!s/#_=j3V!s/$fj2f!sJ$`k20!sT#0`Rj3U!u`$2j2c!s/#E<j2Y!s/$_k10!wR$i2j3b!s/#aVj3P!tP$aj2~!s/#N]j6}!sy#CTj2|!s8#M^j4{!u;$ij2D!s/#Vcj2Q!s/#hUj2_!sS#ILl<T!s/#J1j4x!sJ$Ej4S!s8$Xj3z!s8#KNj6`!s/#0\j6N!s/#[ak20!xM#0e0k30!xx$1!ts#3!s_#K;j4t!s9#W@k30!yH$Lfk505!y[$;j5s!sL$`k40!yO$LCl<O!s/$hlBX!sU#Jcj4e!uK$9j7d!s/#Oej8r!s/$Aj7qTf1R7f0R8#8'1p==g00=oR9/68p=5g006gR:P:g01MNP8H06p=j1H:8p=;g0171R;P:!s$$2P2f3R<f2R=P7!uD#YR>P9P8M<Op>0=!sL&!s$%3P8P7P=P3P<f4R?f5R@f6RAf7RBP9f8RCMBXp>0!t%'!s$%0!s[&0P<P?P@PAPBPCf9R0!sS%9!sK$1P@P1P?P9P9P<P=P7!tO#Tp>081:98p=0P:!tl$T]P8Cep=M!s4$Q0R1!s,#ORDPD!s/#oREP!~=#RORFFdp=IP;P!t\%5!u_#P<g01N2!t-'Op=i!sE&!u~$P@P?!tL,Op=h!ut;!u?,P!u=$=g!sH$6P@P6!u<7!s3#1PDPDPE!u?&PI!u?#P!tt$!sS#!sD'!s[$Grp=31478#8p=a!sb-7P8Fqp=Jg004lRF!xb#OR37[8p=R!s:#GR2#<R5#<#<RG$0@RH$00RI#\RJPI%78%K5RK%KGRL14I8'='2'6RMX?J%8>RN,1LRO,2KRP#5RQ11L9RR!s5#S#5RTP8X<:RU1678#kXD:X<:1H:9RVPPPSPU!s$#1278#j#;XC:X>:PKPK%;KPOPR!sE&1!sE/ROPLPL%;LRPPN!sE#%88#;X<;R;PVH0=N90;N:09J081?KR%5KRN%0RPT[RT[%0KRW!xV#oRXAAKR7UW2%0S\X^2W!v}$SK1y9K'HPNeRSO1RR!#3/#T1RT#^RY%\TRZ%w:R[%v:R\%u:R]1E:9R^1E:KR_g01@=5]:'M'I1p]ER`P8P!|p#:6Ra,HF1o8==[FadAn:97CmRab4b6b712K9#5P8b3b0b5b0CZPQe%^IRQ#714IQ,=L,2K'6e%l7%77#020?H<1BH<RQ#0&0>H,6Q'@14I!s7#GR9#8Rb!w\#c1BH?%7</>L'F%0c%8QRd%K2Re'CRf!sH#g#0PU1:!wc,RhPVPcPg!wB%P!w4$PPPbPf!s6$;P9Pf1C8eRf!sS#9PQPd%;dCiEhM:gJ0<%LQ%0d14I?Rd#8RQ,1L,?K14I@Rb#8Rg!te$#014IARV#8Ri!s7#j,2K#5[\N14IB,=LRk=AK7VXX2W12KkRl#0!wj%R%0j%5l[Rl1W:>Rm%G>R>#G,W:Rn9V:mg00f8Ro'f+0:=UTYRpPZ1c:7RqP\P]1Y:2R299]^Rr&07DRs1E:LRt1E:eRu9b:25P:Rv!sG#C3P`P!we&X1:%08Rw1C7e,1L#0[^1:P81aICRxP?O2!w~'b8CZP41F78#0%0=Ry%07Rz'@R{[1@zw1F=7#0[R|1F<=#0\{1~78P8n20010!s#$12!s-%0X;:X=:P|^;:^=!t:#BH@R|%7?/>LR{%0|%0{%Ld%0Q1?KcPl\N11LxRx!vU/x!vU0k!vU%p-0RQPYPZP!v0$P]!#3&'<E}9J]rPsPr!us2WA1@w7Pz!um#^AQP8f:RQ,BHRE%<G#<!s$&KRG'6PEPAO3!v-,P41>!v+#Py[1>!ut#\zR41>!uu$y1|!uu<>!uu$4^>!uu%%7@R4PL%Lb%0g1?Kj!uh$4I0!yB#l!uk/lRj!uk-x%5j[Rj!uf-!uV7Pz\w!x@$%7QPC!x=/O3b@C{!s+#%Gd,=L/:8PF1BHARd/D7RC1>4LRx!s1#E'Q%R8X;FPFP3%7A/>L/D=,Q8#R!s;$1_7LRA,D4RD1Q3!s<%R1!sS#P11HF3PDPcP4PA%GbRA#8Rc!{}#D/:71Cg!z3#/:7R3!#8{%UP6PhPDPUP9PgO1RDO1Rh,1L!}i2cPh!}i&APDP9PbPg%;g!}`&P7P7%;7M<TP8CxRgP3%LVRV%0iRi1?KkRkPj\NRj!#4,%Rb!w'+R912KbRD!w,&RA!w/#l%5D[RDPp!w//AP:t2Rp!|]611L7R;#0!w>&f;RU,aIRh!|[1b:PgP3PVPiPkPjP9PAPRPD!x;$:1c:=RcP7P[CSRP!xI+!~A#5RO,M2,I]R6PsAJ]r6C3!tN2X9:167=16=<,@y[!tU$^9!|v#1LhR<,2KR6%7UP0PQO4!t_H!tQ$A9]vOPsAz:Ot99]p!tD61Lf!xC#_=L,:;!|_$!tE#PBPhP@!|G/b:E`ENPEP4PLP7!tE7201:L>02:n1W:>=V:m5V:/fo!#5M#T!vB#P[P7P:PcP=!vD#CSRc!ts#&035,Y:R5!#5^#o!vS#Ab:5u9P:t=9]2R5!|1%!u36C=!zI'ePy[\z!u5+hPBP?P@O4R@!u9/CtENPCPLPd!u99!vX$[P\A9]^t!t<,%0LR^!#;T+!w>/1?KL12KLR[#5\^R^\NAAKL!zW%%0[!zP$1?Kl%0b%56[\Nf<,4I!{##N!#3+-NRN!#3+,<%5N[P?PSO1P^!#32+1E:G!y_%!#5n$A]:_H!s7,!{9368G,@w167[,@!#6%#P8f?,BHPU!{:$B!uC&IbB!y_<!w|#!wj$P!w]$P5PsA9]t2!wS8:L=\e!wJ+!w>0!yQ#1Fdx/D7B04dx7ENWGXJ:I05bFbEAUI=7R=!#?B#=!#?B'XHMX?JX;IP8DsW?o"). Qed.

Lemma bytes_le_app : ltac2:(zQ "c0!h9!jc!jnf!ime!jq3!jp0!vd!hga!hmd!hrc!jp9!ik7>2xs@1$3@1$1@1$0#8>2ys@1$3@1$1@1$0#8@3$6$7@1$2@3$4@1$1@1$0#8^2^1@2$8@1$2^2@2$b@1$2^1@2$9+8@1$a@2$5@1$1@1$0#8^2").
Proof.
ltac2:(KReplay.run1z (kr_t_PropExec ()) ["WithFP1"] "##;1h01zh11xh24__x1h32xsh42ysh57__arithh64__ffh78__varmaph85__with94cstrh:2IHh;1mh<1nh=1yp;1p;3p;2p;6p;4p;<p;8p;5p;Bp;7g001:j1@Tg002Dj1p!s/$bj1\!s/#BRj1BTg01NVj39!s/#@[j14!sA#5Lj1K!s8#D]j27!s/#E=R0j15!sC#b9R1j23!s<#AXj21j1Z!s=#UDj20j1[!s>#O3j1o!s/$Tj1h!s/#P8j1d!sM#0\j6F!tM$2j1E!s/#7Ej2C!s/#^5R2j1<!s1#gJj2:!s/#3mj2;!s/#9>j1Yj3J!t[$]j1X!s/#K`j4W!s/#ILl<R!s/#H;j1Q!sV#:Vj2=!s/#C2j2O!s/$Pj1P!s/$nj1N!s/#DYj2>!s/#E<j2T!s/#aVj3M!s/#i2j3L!s/#Jcj4?!s/#Fej2n!s/#GGj2m!s/#H3j3l!s/$Rj4k!tL#F;j4g!se$Uj8I!un$Yj3f!uS$Tj2G!s/#_=j3c!s/$fj2b!u&$`j2a!s8#`Rj3H!t^$_j1e!s/#Oej8`!sJ#Q<j4_!s/$cj3i!wa$;j5^!s/#LCl<D!s/$hlBj!s\#N9j7]!s/#6gR3f1R4f0R53Jp=21;35p=8P3f4R6f3R7f2R8P4P5EFp=6g0171R9P9P3P3P2P0P0P7!y7#2P!sK$M<Dp=V!sE&3!sE#f5R0P6P7!sF-U!sD&!s$%1P5P4P8P1P7P6P0f6f7f8f9MBjp=SP4g00Q0R0!s,#OR1P1!s/#oR2P5g00ROF]p=Ag004GR:#@!s$#R;#pR<#\R=#BR>P=A9=45#4%44R?%45R@%K;R;17=4#5'3'1'0'2^4>RAX3>P3g00=oRB11?5,0B,2?X03P@10B5!s2+2?5X03%8!s<#@%o@D611@B%h!s/#3;B%d;EF%E=RC=9=!tG$C17=C#5,3;,1@!t=#eX4>%48R!s?#8RD#5RE,3;RF,1@RG'0RH1C<6RI115;'0%47/1;RJ,0I17=7#<!sp&?'0R?'2X0311C;RK11G;RL'010I5/!tz$1:F;RM!s{#N10J5,0I!s>&C<7R</0KRI/0N125!uO$3P3%[IRIPIPN%<DR?#5RJ!te#O,1@P3\3RP/;I!sM$Z@!sM$MPO1;PI12MO%K:RI,:ERP!sX#Q,2M!sO$Y3RRP5X13RSPR1245#XX=3X13PMPM%8MPOPQPS!s$$3!wB#1MN1345CW#8X;3X<3P;P;%8;PJPP!sL#%55#8X19P?PP1:5IRP!sr#DPE%8ECVEUM:SM<R%QDRD1=BEREg00T1R?#ER9%B?RS1O34RJ%P3RQ%N3ROP31>3;RM1T3:R:5M3RR=L3Mg00kg1>3I9L3:9M3MC?'A1nO2RMP5P8!z-#lRIg00:6RT';1m58=JITdAl3B4CkRTb6b7b8X2313;5/:;13;P'2^23P517=6#5R6O1b5b9CgGIGI10KN,0<Af<KND6PLP@PFP;!uO#g00eYRE,G3RD%<E#<,G39c3Dg00f8'b'a=H?9PSPJPQPOP0P1P1P2!uL$BR2g00PIR0P:C?,AO%e1!}i&R!s6$G`PMP!tx-=B513;4,=B[!tw$P6P4O2!ts$_!{J#H;AiCG;D6A9=85#4!~,#O1D6AH=78R8!{T'8!{;#!{T3X:!|m#X1=P5D^W3o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma u64_range : ltac2:(zQ "70!h9!hq7!hke!hk0!hl4!hif!jc>1x@1$6@1$0#k0@2$2@2$3Z@2$1@1$0#k0^1@2$4@2$1@1$0#k0^1@2$5+2+k0").
Proof.
ltac2:(KReplay.run1z (kr_t_PropExec ()) ["WithFP1"] "###th01xp;1p;2g001:j10Tg002Dj13!s/$bj12Tg01B8j21!s8#4G#0!s$-3R0#2f0,10W0o"). Qed.

Lemma u6_range : ltac2:(zQ "60!h9!hq7!hke!hk0!hl4!jc>1s@1$5@1$0#6@2$2@2$3Z@2$1@1$0#6^1@2$4@2$1@1$0#6^1+k0").
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01sp;1p;2g001_j14Tg001:j13Tg002Dj10Tg002bj11Tg01B8j22Tg004G#4#3#0R0#1f0,20W0o"). Qed.

Lemma u5_range : ltac2:(zQ "60!h9!hq7!hke!hk0!hl4!jc>1s@1$5@1$0#5@2$2@2$3Z@2$1@1$0#5^1@2$4@2$1@1$0#5^1+i0").
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01sp;1p;2g001:j14Tg001_j13Tg002Dj10Tg002bj11Tg01B8j22Tg004G#4#3#0R0#1f0,20W0o"). Qed.

Lemma wrap64_range : ltac2:(zQ "70!h9!hj6!hke!hga!hk0!hl4!hif>1z$3@2$2@2$4Z@2$1@1$0#k0^1@2$5@2$1@1$0#k0^1@2$6+2+k0").
Proof.
ltac2:(KReplay.run1z (kr_t_PropExec ()) ["WithFP1"] "###kh01zp;1p;2g001:j10Tg002Dj12Tg01RGj21!s8#6gg004G#0!s$-2f0'1W0o"). Qed.

(* [comment removed for export] *)
Lemma bv_swrap_congr : ltac2:(zQ "50!hga!vd!hod!hj6!hp8>1n$4>1x$0>1y$0>0@3$1$0@2$3^3^2@2$3^3^1@3$1$0@2$2^4^3@2$2^4^2").
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01zh11Hh21nh31xh41yp;2p;3p;1p;6p;8g00fdj20Tg009>j32Tg00ggj16Tg00gJj21Tg00hUR0j19Tg003mj23Tg00j2j38Tg000\j65Tg00jdj6:Tg00iUj87Tg00k@j24Tg009Xg006gR1f2R2f1R3'0f0R4,02521P1P1f3R5%65R6,12'0R7#91136,05R8#9P6P6P1P1\1R9P0P0P7P8P9\1/30P11052R0/16,05f4R9%69R:,12'0R;9214X01R<P11053R=114:,09=21;X01P1P8P<131811=6,05A8536E5P0P4E5P7A8526E:G71316G714521453521eW1X41W3W2o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma b_addsext : forall (a : word) {n} (imm : bv n),
  a + sext 64 imm = v_addi a (bv_signed imm).
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01nh11zh22b1h32b2h41Hh51ah63immp;1p;3p;2p;6g001:j13Tg002Dj1CTg002bj11Tg009>j36Tg007Ej20Tg017lj3>Tg0199j3=Tg013dj39Tg01:ij28Tg01S6j2<Tg01>Zj3;Tg00gJj25Tg00fdj24Tg01;Qj2:Tg01T=j3BTg01=kj2ATg000\j67Tg01?Gj3@Tg01Toj3?Tg006gR0f1R1f0R236p=2g004G#3#3#3#3#3#3#CR3#1g009XR4%12R5%11R6g00;Nf2R7#1?612f3R8/071081'2R9[10711072'2%18?671[R:f4R;#1?687\9A>712P2n2001000000120000000W3X25X04P:^36^25^04P2P3A=7319938R41871R5,<8R6P01038R:A;731R9,03R<'5,43103;R;1887R='5,:3,03R>,22X10P0143515;2,43/2>X10P015:5R>,43143=,5;,43/22X10AB3:51:3>,031A3>E7P<A@731E7A9389,03A?389E710341036'2eO4b4W6W0W5o"). Qed.

Lemma b_npc4 : ltac2:(zQ "60!h9!jc!vd!ihc!u7!jq9>1p@1$1@1$0#k0@3$2@1$1@1$0#k0@3$5@1$0#k0^1@2$4@1$0#k0+4@2$3^1+4").
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01zh12b1h22b2h31nh41Hh51pp;1p;3p;2p;6g001:j13Tg002Dj1@Tg002bj11Tg009>j36Tg007Ej20Tg017lj3=Tg005Lj1<Tg01;Qj27Tg013dj3;Tg01S6j2:Tg00gJj25Tg00fdj24Tg01T=j3?Tg01=kj29Tg000\j68Tg01Toj3>Tg006gR0f1R1f0R236p=2g004G#3#3R3#3#3#3#3#@R4#1g009XR5%12R6%11R7g00;Nf2R8#1?612f3R9/081091'2R:[10811082'2%19?681[R;f4#1?698\:A=812P2n2001000000120000000W2W1W3P;^27^16^35P2P4%<3R3,74R59;41R61:13R7P01041R;1045R:'5,441048R8/53,74,04R9,22X00P01443R<1582,44/29X00P015;3R9,44158<,44/22X00A?4;31749,041949E8P:1943E81046R6A>415E81047,26eO4b4W5o"). Qed.

Lemma alu_addi : forall (a : word) {n} (imm : bv n),
  alu64 ALU_ADD a (sext 64 imm) = v_addi a (bv_signed imm).
Proof.
ltac2:(KReplay.run1z (kr_t_PropExec ()) ["WithFP1"] "##$5h01ah13immh21np;1p;3g001:j10Tg002Dj13!s/$bj11Tg01U]j32!s8#4G#0!s$-3#1g009Xf0R0#1f2f1;20W1W2W0o"). Qed.

Lemma alu_andi : forall (a : word) {n} (imm : bv n),
  alu64 ALU_AND a (sext 64 imm) = v_andi a (bv_signed imm).
Proof.
ltac2:(KReplay.run1z (kr_t_PropExec ()) ["WithFP1"] "##/ch01zh11nh21Hh32b1h42b2h51ah63immp;1p;3p;2p;4p;6g001:j13Tg002Dj1L!s/$bj12!s/#9>j35!s/#7Ej20Tg017lj3E!s/#99j3@!s/#Vgj3>!s/#:ij28!s/#WOj2<!s\#>hj26!s/#fdj24!sA#;Qj2;!s/#XVj1K!sA#:Vj2:!s/#5Lj19!s/$jj2J!s/#;2j2I!sS#Y`j1D!s/#Zmj4B!s/#[`j3A!s/#\Lj4?!s/#=kj2C!s\#0\j67!s8#>Zj3F!s/#?Gj3G!sS$hj3H!s/#]Mj3=!sS#6gR0f1R1f0R235p=1g004G#3R3#!s$+R4#LR5#2!v-#XR6%22R7%21R8!tq#NR9f2R:#2?512f3R;/0:10;1'1R<[10:110:2'1%2;?5:1[R=f4R>!sT#;:\<AE:12P2n20010!s#$12!s-%0W4X37X16P=^48^37^16P2P5g01^;A@:51R67>;R718:1R8,<;R=P0105;R<1056'6R?105>R>18;:R@,45'6RA,;5,05RB,12X00P01458R816>2/1B!s8%6<8RB,45R>11A!sL%P>PBP<P8%K;P9g00=oR91452R8':R<%93%94'J,I81451,:9%D2P1!uK7!st#<^00P2P@O1b2CB9A5BC?1;5B!tf#@1C5BE7AF:51,05AG:51E711?@eAH5;6!s:#=5;6E7105!s&#='1eO4b2W6W1W5o"). Qed.

Lemma alu_ori : forall (a : word) {n} (imm : bv n),
  alu64 ALU_OR a (sext 64 imm) = v_ori a (bv_signed imm).
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01nh11zh22b1h32b2h41Hh51ah63immp;1p;3p;2p;4p;6g001:j12Tg002Dj1HTg002bj13Tg009>j34Tg007Ej20Tg017lj3>Tg0199j3=Tg01Vgj3;Tg01:ij28Tg01^gj2:Tg00UDj25Tg00fdj26Tg01;Qj29Tg01XVj1GTg01Y`j1FTg01_mj4CTg01[`j3BTg01\Lj4@Tg01=kj2?Tg000\j67Tg01>Zj3ATg01?Gj3<Tg01`_j3DTg01aCj3ETg006gR0f1R1f0R234p=1g004G#2#2#2#2#2#2#HR3#3g009XR4%32R5%31R6g00;Nf2R7#3?412f3R8/071081'1R9[10711072'1%38?471[R:f4R;#3?487\9A>712P2n2001000000120000000W3X25X04P:^36^25^04P2P3g01b0A=731R47;8R51871R6,:8R:P01038R91034'5R<103;R;1887,63'5R=,93,03R>,12X10P01636R?15;2/1>X10P0159?R>,63R;11=2X10P0P;P>P9P?%G8%F6CC9B3>C@193>,03R61?3>E7AA731,03A<731E711<6eAD384,03AE384E71035103:'1eO4b4W6W0W5o"). Qed.

Lemma alu_xori : forall (a : word) {n} (imm : bv n),
  alu64 ALU_XOR a (sext 64 imm) = v_xori a (bv_signed imm).
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01nh11zh22b1h32b2h41Hh51ah63immp;1p;3p;2p;4p;6g001:j12Tg002Dj1HTg002bj13Tg009>j34Tg007Ej20Tg017lj3>Tg0199j3=Tg01Vgj3;Tg01:ij28Tg01b\j2:Tg00Wbj25Tg00fdj26Tg01;Qj29Tg01XVj1GTg01Y`j1FTg01ccj4CTg01[`j3BTg01\Lj4@Tg01=kj2?Tg000\j67Tg01>Zj3ATg01?Gj3<Tg01dVj3DTg01e;j3ETg006gR0f1R1f0R234p=1g004G#2#2#2#2#2#2#HR3#3g009XR4%32R5%31R6g00;Nf2R7#3?412f3R8/071081'1R9[10711072'1%38?471[R:f4R;#3?487\9A>712P2n2001000000120000000W3X25X04P:^36^25^04P2P3g01eiA=731R47;8R51871R6,:8R:P01038R91034'5R<103;R;1887,63'5R=,93,03R>,12X10P01636R?15;2/1>X10P0159?R>,63R;11=2X10P0P;P>P9P?%G8%F6CC9B3>C@193>,03R61?3>E7AA731,03A<731E711<6eAD384,03AE384E71035103:'1eO4b4W6W0W5o"). Qed.

Lemma alu_slti : ltac2:(zQ "80!h9!jc!vd!jt6!jj4!ju1!ju9!hpb>1a@1$1@1$0#k0>3imm@1$1@1$0#c@3$2@1$1@1$0#k0@3$5$3^2@3$4@1$0#c@1$0#k0^1@2$6^2@2$7@1$0#c^1").
Proof.
ltac2:(KReplay.run1z (kr_t_PropExec ()) ["WithFP1"] "##0Hh07__arithh14__ffh28__varmaph35__with41ah53immh61zp;1p;2p;3p;4p;7p;6p;<g001:j10Tg002Dj19!s/$bj18!s/#1_j1=Tg01:ij21!s/#fUj24!sA#5Lj15!s8#;Qj26!s8#9>j33!s/#3mj22!sA#>Zj3<!s/#g2R0j2;!sC#:VR1j2:!s1#B2j1P!s/$Rj1O!s/#IDj1I!s/#CPj1H!s/$nj1E!s/#DYj27!s/#Jcj4C!s/#N9j7B!s/#Fej2A!s/#GGj2@!s/#H3j3D!s/$Rj4?!tP#F;j4F!tY$Nj4G!sA#0\j6>!s8#99j3J!s/#hBj3K!s/#Vgj3L!s8$oj2M!s/#ILl<N!u[$Xg006gR2P0g01<7P1g01j6f5f4f3f2R1f1R0f0R3M<Np=Qg004GR4#0!s$,R5#9R6#8R7%=!s?$R8#9R9#8P21193R:!sZ#lR;P71161R</43%54,66R4g00=oR=!s2#>n010!s#$2!s'#P!sU$90,4<P4P!sC2537X62!sI%60/4:!sI5R<,27A<963,16P9P6P31;96%58R8%55R5':R?P9P81228P6P51225E!uU#T1R@#P%O@%I2%H2%E2R@g00Q0!s'#ORAPA!s/#oRAP21728g00PI1725CCg00ROFB1A@AP3!vf#0:6RA,2;1@31=3;AdAD2=0C?b1b2b3P?P3b0CFCGE>!uB#AJ963R99K60!uF5=37<e!w`#V?L091M0:537eW5W4o"). Qed.

Lemma alu_sltiu : forall (a : word) {n} (imm : bv n),
  alu64 ALU_SLTU a (sext 64 imm) = v_sltiu a (bv_signed imm).
Proof.
ltac2:(KReplay.run1z (kr_t_PropExec ()) ["WithFP1"] "##+5h01ah13immh21nh31zp;1p;2p;3p;6g001:j10Tg002Dj1A!s/$bj14Tg01:ij25!s8#fdj27!s/#7Ej23!sA#fUj22!s8#5Lj1;!s8#;Qj26!s8#9>j31!s/#3mj28!sA#>Zj39!s/#?Gj3:!sA#0\j6@!s8#99j3?!s/#kBj3>!s/#Vgj3<!s8$oj2=!sS#4GR0#!s$/AR1#4R2!t:#Xf0R3#4g006gR4f1R5/53R6,71R7!sa#lR8P2f3,31R9/23%;0,61R0g00=o!s0#:n010!s#$2!s'#P!sT#2R;/55,71,29P0P!sI2512X34!sO#131;/27!sI5R7,82A951!tF#A:513E@!sW#A?513R59>1;!s[5=127eg01m7?<;51=;6512eW1W2W0o"). Qed.

Lemma alu_add : ltac2:(zQ "60!h9!jc!vd!jv3!ju1!jve>1a@1$1@1$0#k0>1b@1$1@1$0#k0@3$2@1$1@1$0#k0@3$4$3^2^1@2$5^2^1").
Proof.
ltac2:(KReplay.run1z (kr_t_PropExec ()) ["WithFP1"] "##$0h01ah11bp;1p;2g001:j10Tg002Dj14!s/$bj12Tg01mcj21!s8#3mj23!s/#4G#0!s$-4#2R0f1f0'1,30X10W0o"). Qed.

Lemma alu_sub : ltac2:(zQ "60!h9!jc!vd!kg7!ju1!kh2>1a@1$1@1$0#k0>1b@1$1@1$0#k0@3$2@1$1@1$0#k0@3$4$3^2^1@2$5^2^1").
Proof.
ltac2:(KReplay.run1z (kr_t_PropExec ()) ["WithFP1"] "##$0h01ah11bp;1p;2g001:j10Tg002Dj14!s/$bj12Tg01nij21!s8#3mj23!s/#4G#0!s$-4#2R0f1f0'1,30X10W0o"). Qed.

Lemma alu_slt : ltac2:(zQ "60!h9!jc!vd!jt6!ju1!khb>1a@1$1@1$0#k0>1b@1$1@1$0#k0@3$2@1$1@1$0#k0@3$4$3^2^1@2$5^2^1").
Proof.
ltac2:(KReplay.run1z (kr_t_PropExec ()) ["WithFP1"] "##$0h01ah11bp;1p;2g001:j10Tg002Dj14!s/$bj12Tg01ooj21!s8#3mj23!s/#4G#0!s$-4#2R0f1f0'1,30X10W0o"). Qed.

Lemma alu_sltu : ltac2:(zQ "60!h9!jc!vd!ki4!ju1!kj0>1a@1$1@1$0#k0>1b@1$1@1$0#k0@3$2@1$1@1$0#k0@3$4$3^2^1@2$5^2^1").
Proof.
ltac2:(KReplay.run1z (kr_t_PropExec ()) ["WithFP1"] "##$0h01ah11bp;1p;2g001:j10Tg002Dj14!s/$bj12Tg0215j21!s8#3mj23!s/#4G#0!s$-4#2R0f1f0'1,30X10W0o"). Qed.

Lemma alu_and : ltac2:(zQ "60!h9!jc!vd!kja!ju1!kk5>1a@1$1@1$0#k0>1b@1$1@1$0#k0@3$2@1$1@1$0#k0@3$4$3^2^1@2$5^2^1").
Proof.
ltac2:(KReplay.run1z (kr_t_PropExec ()) ["WithFP1"] "##-Eh01Hh12b1h22b2h31nh41xh51zh61ah71bp;1p;3p;2p;4p;6g001:j12Tg002Dj1F!s/$bj13!s/#9>j31!s/#7Ej20Tg017lj3C!s/#Vgj3=Tg022<j2<!sJ#>hj25!sA#;Qj27!s8#fdj2:!s8#XVj14!s8#:Vj26!s/#5Lj19!s/$jj2E!s/#;2j2D!sS#Zmj4B!s/#[`j3@!s/#\Lj4>!s/#=kj2?!sS#0\j68!sA$hj3A!s/#]Mj3;!sA#4G#2R0#2!s$'R1#FR2#3R3!uG#XR4f0R5#3R6f1R7#3R8!tJ#NR9f2R:#3?175g006gR;f3R</0:10<731R=[10:710:551;%3<?1:7[R>f4!sZ#<:\=AC:75P5n20010!s#$12!s-%0W2W1W3P>^28^16^34P5P2g01^;?=:7R41<:7R6P;102:R81027R>'5R=102</58R<,72,0291;5X5;P;1:2=R?A1;<!s6%P?P=P8P>%4:P9g00=oR91025R8'6R?%90%91'E,D8169>%45P7!tt7X43P?^43P5P:O1b0CB9@2=C>172=,021?2=E8AA2:7,02A;2:7E!tz#4102651;eO4b0X73W6o"). Qed.

Lemma alu_or : ltac2:(zQ "60!h9!jc!vd!kke!ju1!kl8>1a@1$1@1$0#k0>1b@1$1@1$0#k0@3$2@1$1@1$0#k0@3$4$3^2^1@2$5^2^1").
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h02b1h12b2h21nh31zh41Hh51ah61bp;1p;3p;2p;4p;6g001:j13Tg002Dj1BTg002bj12Tg009>j31Tg007Ej20Tg017lj3<Tg01Vgj3;Tg023Bj29Tg00UDj25Tg01;Qj24Tg00fdj28Tg01XVj16Tg01_mj4:Tg01[`j3ATg01\Lj4@Tg01=kj2?Tg000\j67Tg01`_j3=Tg01aCj3>Tg004G#3#3#3#3#3#3#BR0#2R1g009XR2f0R3#2R4f1R5#2R6g00;Nf2R7#2?153g006gR8f3R9/07109531R:[10751073518%29?175[R;f4#2?197\:A<753P3n2001000000120000000W1W0W2P;^16^04^22P3P0g01b0?;75R21975R4P81007R61005R;'5R:1009/56R9,40,009183X38P8180:R<A1893X38P8P<P:P6P;%67%65C:9A0:C@140:,001?0:E7A=075,00A>075E710021004518eO4b4X61W5o"). Qed.

Lemma alu_xor : ltac2:(zQ "60!h9!jc!vd!km0!ju1!kmb>1a@1$1@1$0#k0>1b@1$1@1$0#k0@3$2@1$1@1$0#k0@3$4$3^2^1@2$5^2^1").
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h02b1h12b2h21nh31zh41Hh51ah61bp;1p;3p;2p;4p;6g001:j13Tg002Dj1BTg002bj12Tg009>j31Tg007Ej20Tg017lj3<Tg01Vgj3;Tg024Gj29Tg00Wbj25Tg01;Qj24Tg00fdj28Tg01XVj16Tg01ccj4:Tg01[`j3ATg01\Lj4@Tg01=kj2?Tg000\j67Tg01dVj3=Tg01e;j3>Tg004G#3#3#3#3#3#3#BR0#2R1g009XR2f0R3#2R4f1R5#2R6g00;Nf2R7#2?153g006gR8f3R9/07109531R:[10751073518%29?175[R;f4#2?197\:A<753P3n2001000000120000000W1W0W2P;^16^04^22P3P0g01ei?;75R21975R4P81007R61005R;'5R:1009/56R9,40,009183X38P8180:R<A1893X38P8P<P:P6P;%67%65C:9A0:C@140:,001?0:E7A=075,00A>075E710021004518eO4b4X61W5o"). Qed.

(* [comment removed for export] *)
Lemma shamt6_mask : ltac2:(zQ "80!h9!hq7!vd!hga!kn4!u7!jc!knb>1s@1$6@1$0#6@3$2$3@2$1@1$0#k0@3$7@1$0#k0@3$4@1$0#6@1$0#k0^1@2$5@1$0#k0+jf@2$1@1$0#6^1").
Proof.
ltac2:(KReplay.run1z (kr_t_PropExec ()) ["WithFP1"] "##4?h07__arithh14__ffh28__varmaph35__with41zh52Hah66__sat1h7!s/%0h81sp;1p;3p;2p;4p;6p;7p;<g001_j13T!s/#:j10!s/#2Dj1=!s/$bj1CTg025Mj3`!s8#7Ej22!s/#5Lj16Tg01;Qj2G!s8#>hj2:!s/#9>j35!sJ$jj2>!s/#6Gj2A!sn#68j1@!s/#7Aj3_!s/$dj1U!sJ#B2j1T!s/$Rj1M!s/#IDj1L!s/#CPj1K!s/$nj1J!s/#DYj24!s/#Fej2F!s/#3mj28!s/#GGj2E!s/#H3j3H!s/$Rj4I!s/#:VR0j21!tE#8Bj3D!s:#0\j69!s/#@Ej2B!s/#;2j2<!s8$mj3N!s/#AQj2O!s/#J@j3P!s/$cj4?!s/#OAj7Q!s\$Nj2R!t$$ej3S!s/#9Qj3^!v@#g2R1j2]!s1#F;j4V!sC#:>j4W!s8#\hj3X!s/#]Mj3Y!sp#N9j7Z!s8#ILl<[!v]$gR2f1R3g00PIf0R4C?p=;P!s6#Q0R5!s,#OR6P6!s/#oR7P4g00ROFZp=7!wU#XP2P1g01<7P0g01j6f5f4f3f2R0P3P4M<[p=\g004GR1#3R8#0R9#=R:#CP2%01R1#0!s$'R;#=R<A`:<4R='2%38#3!s$$6R8,G<R>,2<R?':R@12:3RA9524X42RBP212:4RC1:4?=52AX42P2P81:A4!s5+%61R1%69R9'>RA,ACPB%@49_CA%U9,:Cg00T1RA#TRB%MARA%L2RD%K2RE%J2RFg00=oRG,42RH1429RI';'71FF7RJP4!uq#04lRK!xv#6RL'81E40=5KLdAH2G3CIRLb1b2b311G9P4b09DC9E9P?%6;R;,B11<G1R?11G;1>1;RK,<G[R0[11G1RM!w8#oRNAN1;3UW511GK\N^5M!wk$SK1OG1'8P?eO1P0PBPAPDPEPFP5P6P6P71428R7,;H,7FP2P!w|#T]1421=P2<C?,7FFQPJP!to,81<8K'R!tu#b6b7b69S<8E9A^:<4,2<P:P<P41]:<119;R8P:P91829P<P;182;E\!tR'142;,;I!tF#!t-+P8!s~#CVCWE9A52@CeAX<=!xI#AY<=>E9W8o"). Qed.

Lemma regamt64_mask : ltac2:(zQ "80!h9!hq7!vd!hga!hi5!u7!jc!knb>1b@1$6@1$0#k0@3$2$3@2$1@1$0#k0@3$7@1$0#k0^1@2$5@1$0#k0+jf@2$4@2$1@1$0#k0^1+k0").
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h02Hah17__arithh24__ffh36__sat1h48__varmaph55__with61zh76__sat0h81bp;1p;2p;3p;4p;6p;7g001:j10Tg002Dj1VTg002bj1HTg007Ej25Tg001_j12Tg005Lj13Tg01;Qj2JTg00>hj29Tg006Gj2:Tg009>j37Tg005jj2>Tg003mj2=Tg027dj1?Tg00B2j1UTg00BRj1TTg00IDj1STg00CPj1MTg00Cnj1LTg00DYj24Tg00Jcj4;Tg00Fej2ITg00GGj2GTg00H3j3FTg00HRj4ETg00:Vj21Tg028Bj3DTg000\j66Tg00@Ej2CTg00;2j2<Tg00@mj3KTg00AQj2BTg00J@j3ATg00OAj7NTg00;Nj2@Tg028ej3OTg01\hj3PTg01]Mj3QTg00N9j7RTf1R0g00Q0R1g00QOR2P2g00QoR3f0R4g00ROFRp=8g004GR5#0R6#0#0#0#0#0R7#VR8#Hg006gR91584R:%25R5#2#2#2#2#3R;,J8R<,58R='91580R>%37R7':R?9794X69R@P9P;19>4=79?X69P9%36R6%05#3R5'>,::P@1::7,=9%?5,9:g00T1R@#UR?%T@R@%S9R>%M9RA%L9RBP9g00=oRC,49RDg00PIRE1495C;'81IB3RFP4f2RGg004lRHg00:6RI'=1G4G=7HIdAF9C0CERIb2b4b511C5P4b19D:5E6P=1C671<C6R=11C71>67R5,<C[R:[11C6RHg00RoRGAK670UW011C5\G^0HP0g00SK1BC6'=P=eO1P:P?P@P>PAPBP1P2P2P3P9PDPE149;REC;,8BP9PEg00T]1496=A98C;,8BFNPFPIb2b4b511C;1<;5'@P4b1b3b7b39O8;E6AP84<,58AQ84<E6W8o"). Qed.

Lemma alu_slli : ltac2:(zQ "80!h9!jc!vd!ko4!kn4!ju1!kof!hq7>1a@1$1@1$0#k0>1s@1$1@1$0#6@3$2@1$1@1$0#k0@3$5$3^2@3$4@1$0#6@1$0#k0^1@2$6^2@2$7@1$0#6^1").
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01zh12b1h22b2h31nh41Hh51ah61sp;1p;3p;2p;6g001:j11Tg002Dj1;Tg002bj12Tg001_j15Tg009>j37Tg007Ej20Tg017lj3@Tg025Mj3:Tg01Vgj3?Tg02;4j2>Tg005Lj1=Tg01;Qj28Tg01\hj3<Tg01AXj26Tg00fdj24Tg003mj2ETg02<;j1DTg000\j69Tg01=kj2CTg02=Gj3BTg02=oj3ATg006gR0f1R1f0R237p=3g004GR3#1#1#1#1#1#1#;R4#2%53R3#1#;R5#2g009XR6%22R7%21R8g00;Nf2R9#2?712f3R:/0910:1'3R;[10911092'3%2:?791[R<f4#2?7:9\;A@912P2n2001000000120000000W2W1W3P<^28^17^36P2P4g02>`A:541R67?9R71051R8,>9R<P01049R;%53#5#5#5#=,84R39<46R6,04R='6,44104:R:1059'6R>,84,04,32X00P016;8R;,44R?A:549=<43,04,6:,44/32X00P0P816:2,44144>'3X001E0?P=%D1E9184;,041C4;E9AB496,04AA496E91047104<'3eO4b4W6W5o"). Qed.

Lemma alu_srli : ltac2:(zQ "80!h9!jc!vd!kp9!kn4!ju1!kq4!hq7>1a@1$1@1$0#k0>1s@1$1@1$0#6@3$2@1$1@1$0#k0@3$5$3^2@3$4@1$0#6@1$0#k0^1@2$6^2@2$7@1$0#6^1").
Proof.
ltac2:(KReplay.run1z (kr_t_PropExec ()) ["WithFP1"] "##/eh01sh11zh21Hh32b1h42b2h51nh61ap;1p;3p;2p;4p;6g001:j12Tg002Dj1:!s/$bj11!s/#1_j14!s/#9>j36!s/#7Ej20Tg017lj3CTg025Mj3;!s8#Vgj3@!s8#?Lj2?!sS#5Lj19!sA#;Qj27!s/#\hj3>!sA#cgj25!s/#fdj2=!sA#XVj1K!s8#:Vj2<!s/#;2j2J!sw#68j1I!s/#@Sj4H!sS#[`j3E!sw$Lj4B!sA#<;j1D!s\#0\j68!sA#=kj2A!sA#AHj3F!s/#B0j3G!sJ#6gR0f1R1f0R236p=3g004GR3#2!s$,R4#:R5#1%43!s?$:R6#1R7!v'#XR8%12R9%11R:!tw#NR;f2R<#1?612f3R=/0<10=1'3R>[10<110<2'3%1=?6<1[R?f4!sR#=<\>AC<12P2n20010!s#$12!s-%0W4W3W5P?^4:^39^58P2P5!u=#aA;651R87@<R91061R:,?<R?P0105<R>%43#4!s$$9,75R39>58R8,05R@'5105=R=106<'5RA,75,05,32X10P015>:RB,=5RC!t1#<=>53!sE#5=/!sH&P:15=21=5A'3!s7%CPBP>P:%K<P;g00=oR;1062R6'!tX#94,J61<;:%I2P1!u\7X07P>^07P2P<O1b2CH9E5BCBP@%D1E8175B,051A5BE8AF5<!u>#AG5<8E81059105?'3eO4b2W0W6o"). Qed.

Lemma alu_srai : ltac2:(zQ "80!h9!jc!vd!kqe!kn4!ju1!kr9!hq7>1a@1$1@1$0#k0>1s@1$1@1$0#6@3$2@1$1@1$0#k0@3$5$3^2@3$4@1$0#6@1$0#k0^1@2$6^2@2$7@1$0#6^1").
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01zh12b1h22b2h31nh41Hh51ah61sp;1p;3p;2p;6g001:j11Tg002Dj1<Tg002bj12Tg001_j14Tg009>j37Tg007Ej20Tg017lj3BTg025Mj3;Tg01Vgj3@Tg02CMj2?Tg01:ij2:Tg005Lj1>Tg01;Qj29Tg01\hj3=Tg00cgj26Tg00fdj25Tg003mj2FTg02<;j1ETg000\j68Tg01=kj2DTg02DTj3CTg02E=j3ATg006gR0f1R1f0R237p=3g004GR3#1#1#1#1#1#1#<R4#2%43R3#1#<R5#2g009XR6%22R7%21R8g00;Nf2R9#2?712f3R:/0910:1'3R;[10911092'3%2:?791[R<f4#2?7:9\;AB912P2n2001000000120000000W2W1W3P<^28^17^36P2P4g02EoA;541R67@9R71051R8,?9R<P01:49R;%43#4#4#4#>,94R39=46R6,04R='6,541:4:R:1059'6R>,94,04,32X00P016;8R;,54R?A;549==43,04,6:,54/32X00P0P816:2,54154>'3X001F0?P=%E1E8194;,041D4;E8AC496,04AA496E81047104<'3eO4b4W6W5o"). Qed.

Lemma alu_sll : ltac2:(zQ "60!h9!jc!vd!ko4!ju1!ks3>1a@1$1@1$0#k0>1b@1$1@1$0#k0@3$2@1$1@1$0#k0@3$4$3^2^1@2$5^2^1").
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01zh12b1h22b2h31nh41Hh51ah61bp;1p;3p;2p;6g001:j12Tg002Dj1ETg002bj11Tg009>j37Tg007Ej20Tg017lj3?Tg01Vgj3>Tg02F[j2=Tg001_j15Tg005Lj1;Tg01;Qj28Tg01\hj3:Tg01AXj26Tg00fdj24Tg006Gj2<Tg003mj2DTg02Gaj1CTg000\j69Tg01=kj2@Tg02=Gj3ATg02=oj3BTg006gR0f1R1f0R237p=3g004GR3#2#2#2#2#2#2R4#ER5#1R6g009XR7%12R8%11R9g00;Nf2R:#1?712f3R;/0:10;1'3R<[10:110:2'3%1;?7:1[R=f4#1?7;:\<A?:12P2n2001000000120000000W2W1W3P=^29^18^37P2P5g02>`?>:1R71=:1R8P0105:R9%53#5#5#5#5#;,85R39:51R=,05R<'6,45105;R;%;4R4,<9'6R>,85,05,32X00P01051/<4R4,69R9,45R?A:5:3,05,6;,45/32X00P0P416;2,45145>'3X001D0?P<%C1E91859,051@59E9AA5:=,05AB5:=E910571058'3eO4b4X66W5o"). Qed.

Lemma alu_srl : ltac2:(zQ "60!h9!jc!vd!kp9!ju1!ksc>1a@1$1@1$0#k0>1b@1$1@1$0#k0@3$2@1$1@1$0#k0@3$4$3^2^1@2$5^2^1").
Proof.
ltac2:(KReplay.run1z (kr_t_PropExec ()) ["WithFP1"] "##5Bh01zh11Hh27__arithh34__ffh44__p1h58__varmaph65__with74__x1h82b1h92b2h:1nh;6__sat0h<1ah=1bp;1p;3p;2p;4p;6p;7p;8g001:j12Tg002Dj1b!s/$bj13!s/#9>j35!s/#7Ej20Tg017lj3R!s/#Vgj3LTg02Hoj2K!sJ#1_j16!s/#5Lj1<!sJ#;Qj29!s/#\hj3A!sA#cgj27!s/#6Gj2;!s/#fdj2B!sJ#XVj1X!s8#B2j1V!s/$Rj1U!s/#IDj1Q!s/#CPj1N!s/$nj1M!s/#DYj2?!s/#Jcj4>!s/#Fej2J!s/#3mj2H!s/#GGj2G!s/#H3j3F!s/$Rj4I!s/#;2j2:!u<#J5j3E!s8$NR0j2@!s:$\j2D!t<$2j2O!s/#E<j2P!s/#N]j6C!s/#OAj7S!sA$_j1T!s8$ej8a!se#@Sj4`!uP#[`j3_!u}$Lj4]!sA#Gaj1\!sS#0\j68!sA#=kj2Y!sA#AHj3Z!s/#B0j3[!t:$9j7W!s/#:Vj2^!v[$gR1f1R2f0R335p=1P2g00Q0R4!s,#OR5P5!s/#oR6P3g00ROFWp==g00=oR7/^3p=!sO#4GR8#2!s$,R9#bR:#3R;!xh#XR<%33R=%32R>P0f2R0#3?523f3R?/0010?2'1R@[10021003'1%3??502[RAf4RB!sT#?0\@AR023P3n2!sZ#!s#$12!s-%0W9W8W:PA^9>^8=^:<P3P:!uq#a?L02R<1K02R=P110:0R>%68#6!s$&<,9:RA9A:2R@,0:RC'710:?RD%<9R9,;>'7RE,9:,0:,13X01!sk$2RF/;9RG,7>RH,B:RIAA:0A!sK#7D/!sN&PG17D31B:E'1!s7%IPHP>PG%X0g00T1RI#VRE%UIRI%Q1%N1RD%M1RAP11?17RJ!sK#]1?19C>'=1JA6RKP3P!sb#4lRL!x6#6RM'H1G30=5LMdAF172CIRMb3b5b61:79P3b29EF9%4G1:G9'@1D>9%4>%4910:B!u;#B#4[[p-0R>PEPI1O12PDPAP4P5P5P6!s0-1P!t`#PI1P18C>,=AR8!sD-?ECFS%T5P8GaPKP!tR&X71W4%43/@2%42[^71^4>P31:B9PBP0O3b2b;b1C`9_:HC]PC%\2E819:H,0:1Y:HE8AZ:0!wa#A[:0@E810:<10:='1eO4b1X=;W<o"). Qed.

Lemma alu_sra : ltac2:(zQ "60!h9!jc!vd!kqe!ju1!kt5>1a@1$1@1$0#k0>1b@1$1@1$0#k0@3$2@1$1@1$0#k0@3$4$3^2^1@2$5^2^1").
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01zh12b1h22b2h31nh41Hh51ah61bp;1p;3p;2p;6g001:j12Tg002Dj1FTg002bj11Tg009>j37Tg007Ej20Tg017lj3CTg01Vgj3@Tg02KMj2>Tg01:ij2;Tg001_j15Tg005Lj1:Tg01;Qj28Tg01\hj3=Tg00cgj26Tg00fdj24Tg006Gj2<Tg003mj2ETg02Gaj1DTg000\j69Tg01=kj2BTg02DTj3ATg02E=j3?Tg006gR0f1R1f0R237p=3g004GR3#2#2#2#2#2#2R4#FR5#1R6g009XR7%12R8%11R9g00;Nf2R:#1?712f3R;/0:10;1'3R<[10:110:2'3%1;?7:1[R=f4#1?7;:\<AC:12P2n2001000000120000000W2W1W3P=^29^18^37P2P5g02Eo?@:1R71>:1R8P01;5:R9%53#5#5#5#5#:,85R39=51R=,05R<'6,451;5;R;105:%:4R4'<'6R>,85,05,32X00P01051/<4R4,69R9,45R?A=5:3,05,6;,45/32X00P0P416;2,45145>'3X001E0?P<%D1E91859,051B59E9AA5:=,05A?5:=E910571058'3eO4b4X66W5o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma low32_unsigned : ltac2:(zQ "70!h9!hq7!vd!hga!kte!jc!hj6>1a@1$5@1$0#k0@3$2$3@2$1@1$0#i0@1$4^1@2$6@1$0#i0@2$1@1$0#k0^1").
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01zh11ap;1p;2p;3p;6p;4g001:j10Tg002Dj16Tg002bj1;Tg007Ej21Tg01<7j1=Tg00cgj25Tg00fdj22Tg009>j33Tg003mj2:Tg01<Uj18Tg000\j64Tg018Pj47Tg01=9j49Tg02LSj1<Tg004G#0#0#0#0#0R0#0#6R1#;g006gR2%60R0f0R3,11R4g01@=R5#='5'2f1,11,20R69323X02P2P41203=326X021204R6,:2g00=o,54%84E4P1P5P0P3C7,10P1P5P0P3C9E4%<3,10=326eW1o"). Qed.

Lemma low32_signed : ltac2:(zQ "80!h9!vd!hga!kte!jc!hpb!hod!hq7>1a@1$4@1$0#k0@3$1$2@2$5@1$0#i0@1$3^1@2$6@1$0#i0@2$7@1$0#k0^1").
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01zh11ap;1p;2p;3p;6p;4g001:j10Tg002Dj17Tg002bj1;Tg007Ej23Tg01<7j1>Tg00cgj26Tg00k@j21Tg009>j32Tg003mj2:Tg01<Uj19Tg000\j65Tg018Pj48Tg01:ij24Tg02M;j4=Tg02LSj1<Tg004G#0#0#0#0#0R0#0#7R1#;g006gR2%70R0f0R3,31R4g01@=R5#>'6'1f1,31,10R69223X02P2P41103=226X021104R6,:2g00=o,64%94E5P1P5P0P3C8,40P1P5P0P3C=E5%<3,40=226eW1o"). Qed.

(* [comment removed for export] *)
Lemma shamt5_mask : ltac2:(zQ "80!h9!hq7!vd!hga!kn4!u7!jc!knb>1s@1$6@1$0#5@3$2$3@2$1@1$0#i0@3$7@1$0#i0@3$4@1$0#5@1$0#i0^1@2$5@1$0#i0+hf@2$1@1$0#5^1").
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h07__arithh14__ffh28__varmaph35__with41zh52Hah66__sat1h76__sat0h81sp;1p;3p;2p;4p;6p;7p;<g001:j12Tg001_j13Tg002Dj1=Tg002bj1CTg025Mj3`Tg007Ej21Tg005Lj16Tg01;Qj2GTg00>hj2:Tg009>j35Tg005jj2>Tg006Gj2ATg02Mkj1@Tg027Aj3_Tg027dj1UTg00B2j1TTg00BRj1MTg00IDj1LTg00CPj1KTg00Cnj1JTg00DYj24Tg00Fej2FTg003mj28Tg00GGj2ETg00H3j3HTg00HRj4ITg00:VR0j20Tg028Bj3DTg000\j69Tg00@Ej2BTg00;2j2<Tg00@mj3NTg00AQj2OTg00J@j3PTg00Jcj4?Tg00OAj7QTg00;Nj2RTg028ej3STg029Qj3^Tg01g2R1j2]Tg01F;j4VTg02:>j4WTg01\hj3XTg01]Mj3YTg00N9j7ZTg01ILl<[Tg006gR2f1R3g00PIf0R4C?p=;P3g00Q0R5g00QOR6P6g00QoR7P4g00ROFZp=7g009XP2P1g01<7P0g01j6f5f4f3f2R0P3P4M<[p=\g004GR1#2R8#3R9#=R:#CP2%28#2#2#2R;#=R<A`:<4R='1%31#3#3#3#6R1,G<R>,1<R?':R@11:3RA9524X42RBP211:4RC1:4?=52AX42P2P11:A4=52AX42P2%68R8%69R9'>RA,ACPB%@49_CA%U9,:Cg00T1RA#TRB%MARA%L2RD%K2RE%J2RFg00=oRG,42RH1429RI';'71FF7RJP4P0g004lRKg00:6RL'81E40=5KLdAH2G3CIRLb1b2b310G9P4b09DC9E9P?%6;R;,B81<G8R?10G;1>8;RK,<G[R0[10G8RMg00RoRNAN8;3UW510GK\N^5MP3g00SK1OG8'8P?eO1P0PBPAPDPEPFP5P6P6P71421R7,;H,7FP2P7g00T]1428=P2<C?,7FFQPJPLb1b2b310G11<1K'RP4b0b6b7b69S<1E9A^:<4,1<P:P<P41]:<109;R1P:P91829P<P;182;E\PBPAPDPE142;,;I,7FPJPLb1b2b3P1P4b0CVCWE9A52@CeAX<=>,1<AY<=>E9W8o"). Qed.

Lemma regamt32_mask : ltac2:(zQ "90!h9!hq7!vd!hga!kte!hi5!u7!jc!knb>1b@1$7@1$0#k0@3$2$3@2$1@1$0#i0@3$8@1$0#i0@1$4^1@2$6@1$0#i0+hf@2$5@2$1@1$0#k0^1+i0").
Proof.
ltac2:(KReplay.run1z (kr_t_PropExec ()) ["WithFP1"] "##5Yh06__sat1h11zh22Hah37__arithh44__ffh58__varmaph65__with7!s\%0h81bp;1p;2p;3p;4p;6p;7g001:j10Tg002Dj1@!s/$bj1STg02LSj1I!s8#7Ej27!s/#1_j11!s/#5Lj16Tg01;Qj2R!s8#>hj29!s/#6Gj24!s/#9>j33!s/#fdj2C!s\$jj2?!s/#@Ej2E!s/#;2j2;!s8$mj3D!s/#AQj2W!s/#3mj2>!s/#B2j1V!s/$Rj1U!s/#IDj1T!s/#CPj1Q!s/$nj1N!s/#DYj2:!s/#J@j3A!s/#Fej2L!s/#GGj2K!s/#H3j3J!s/$Rj4H!s/#b9j2B!ui#O4j4M!s/$Nj6G!uW#\Lj4O!s8#P6j1P!sS#0\j68!s8#7dj1F!t:$cj4=!s8#8Bj3`!s8#OAj7_!uW$Nj2^!sA$ej3]!s/#QDj1\!t$$hj3Y!s/#]Mj3X!sS#:Vj2Z!s/#N9j7[!s/#=oR0f0R1'Zp=2!v{#gR2f1R3g00T]P1C=p=<P!s4#Q0R4!s,#OR5P5!s/#oR6P1g00ROF[p=!s9#4GR7#0R8#0!s$%R9#0#@R:#SP2%@9R;%I1R<'7R=%17R7#1!s$$6R>,R;R?,7;R@'917:3RA%69R9'4RB9321X12RCP217:1R:,C;RD191@=32BX12P2P>1C;A/91!s8+%68RA%18R8#6RE'?RF,4DP!si#?A9RC,4:RG141F!sW+14:914GFPFPCP:1EAE1;0ARG%2ERB1;0FRH[RI[%2ARJ!ui#oRKADAE3UW2%2F\K^2J!vC$SK1W0A'>PGeO1RLPI!ve#1RI#VRM%UIRI%T2RN%Q2RO%N2RP1:20RQ1:2ARR%@85A2'<'51LP6R8P1f2RS!vu#l!{f$:6RU'>1K1S=3TUdAJ203CHRUb4b5b6PHP1b3b0b7b01EA9RH%291;0CR0[RT\GRGADA93VKX2JR9%2C!u'$RJPLPTPMPIPNPOAA2R;RR,<Q,5PP8P!t%'0!t%,P21B1F932CX12%0!x2%6,?ARA1BAF,>2CMEGCOPD%P:E8%FE,9D!t-'P2PQg00PIR:1:2EC=!t51B!t5#9`DEE8P@PHPGP9P!tn0PPP4P5P5P6!sp#P!sk#>R2!sm$1<2R,5PF_!sv,%2>1;>C'^!u4,9];>E8P=%\1E8AY;<!z3#AX;<?E8W8o"). Qed.

(* [comment removed for export] *)
Lemma sext32_unsigned : ltac2:(zQ "80!h9!hq7!vd!hga!jj4!jc!hod!hj6>1v@1$5@1$0#i0@3$2$3@2$1@1$0#k0@3$4@1$0#i0@1$0#k0^1@2$7@1$0#k0@2$6@1$0#i0@2$1@1$0#i0^1").
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01vh11zp;1p;2p;3p;6g001:j10Tg002Dj15Tg002bj1<Tg01:ij26Tg00fdj22Tg007Ej21Tg00k@j24Tg009>j33Tg003mj2;Tg01>Zj3:Tg01?Gj37Tg000\j68Tg0199j39Tg004G#0#0#0#0#0R0#5R1#<g006gR2%00#5R0f0R3,61'2f1,11,41,209323X121113,41,20R4,;2A:103,10A7103E8A9103,10=324eW0o"). Qed.

Lemma w_addiw : ltac2:(zQ "90!h9!jc!jj4!vd!jv3!ku6!kte!kue!hpb>1a@1$1@1$0#k0>3imm@1$1@1$0#c@3$3@1$1@1$0#k0@3$2@1$0#i0@1$0#k0@3$5$4@1$6^2@3$2@1$0#c@1$0#i0^1@2$7^2@2$8@1$0#c^1").
Proof.
ltac2:(KReplay.run1z (kr_t_PropExec ()) ["WithFP1"] "##1Ah01zh12b1h22b2h31nh41Hh51ah63immp;1p;3p;2p;8p;6g001:j15Tg002Dj1:!s/$bj17!s/#1_j1B!s/#9>j38!s/#7Ej20Tg017lj3JTg02LSj1<!s8#99j39!s8#RSj3=!s8#:ij2;!s8#S;j2@!se#k@j21!s/#fdj22j1O!s2#gJj26!sV#;Qj2?!s8#3mj2>!s_#TCj3N!s8#m0j3M!s8#UXj2I!sS#>Zj3H!s/#?Gj3E!sA#QDj1D!s8#3dj3F!s/#Toj3G!se#iUj8C!s8#=kj2K!sS#Vgj1L!sA#0\j6A!s/#6gR0f1R1f0R238p=3P0f4R3f3R4f2R5P1P2EAp=4g004GR6#5!s$'R7#5#:R8#7%B!s=%:R6#7!vU#XR9%72R:%71R;g00;N%75?81210451041'3R<[10511052'3%74?851[R=%73?845\<AJ512P2n20010!s#$12!s-%0W2W1W3P=^2;^1:^39P2P8%:7R7g02X7R9%<5R:A96!tL#3=R=798R<1;61R3,@5R>107=,17R?,281084R@1;65'6!s:#A,?8,08,32X!tH#85RB/63!s@#C,28%<4!s~#5R45=9,07,17,28/!sS$P0P0%O8R9P9P?PCP0\0/>9107:R!s+#;R?'6,271172/3A!t+#27BRD1074,62,2!ss#!s?+3R4127@/!s?26D4R@!t[#E132!s8#RA16B4!s8#2PAPCPA1>0CP2AN7B3D4PEAM7B4D!sr$,171I7@D4AH671,07AE671D416D?!t3'CeP9%D5D4AF7:;!sJ#G7:;D4GC1?8C,081K8CD4108<R<%L=!s1$>,3<eO4b4W6W5o"). Qed.

Lemma w_slliw : ltac2:(zQ "a0!h9!jc!vd!ko4!jj4!kn4!ku6!kte!kv9!hq7>1a@1$1@1$0#k0>1s@1$1@1$0#5@3$2@1$1@1$0#k0@3$4@1$0#i0@1$0#k0@3$6$3@1$7^2@3$5@1$0#5@1$0#i0^1@2$8^2@2$9@1$0#5^1").
Proof.
ltac2:(KReplay.run1z (kr_t_PropExec ()) ["WithFP1"] "##9Zh01zh11sh21Hh32Hah46__sat1h52b1h62b2h71nh87__arithh94__ffh:!sN%0h;8__varmaph<5__with=1ap;1p;3p;2p;4p;7p;6p;8g001:j16Tg002Dj1C!s/$bj15!s/#1_j1<!s/#9>j3:!s/#7Ej20Tg017lj3XTg02LSj1G!s/#5Mj3F!s/#RSj3D!sJ#99j3J!s8#Xcj2I!se#k@j24!s/#fdj21j1[!sM#AXj29!s/#;Qj2A!sD#3mj2@!s/#5Lj1?!sA#\hj3Y!s8$jj2=!s/#b9j28!s/#6Gj27!s/#@Ej2W!s/#;2j2>!s/#:Vj2;!sA$mj3V!s/#AQj2U!s/#B2j1T!s/$Rj1N!s/#IDj1L!s/#CPj1K!s/$nj1M!s/#DYj2E!s/#J@j3O!s/$cj4P!s/#N9j7Q!uZ#Ykj6R!s8#Fej2S!s/#GGj2i!s/#H3j3h!s/$Rj4g!sS#ZOj4f!s/#P6j1B!s/#Mkj1c!s/#[8j3H!s/$aj4b!s/#UXj2]!s/#QDj1\!s/#]0j1^!s/#=Gj3_!s/$oj3`!t1#iUj8a!vP#=kj2Z!sA#Vgj1d!sA#0\j6e!vP$gR0f1R1f0R23:p=2P0f4R3f3R4f2R5P1P2Eep=3g004GR6#6R7#6!s$%R8#6#CR9#5%<7#CR:#5R;!y7#XR<%52R=%51R>!wJ#NR?%55?:1210451041'2R@[10511052'2%54?:51[RA%53?:45\@AX512P2n20010!s#$12!s-%0W6W5W7PA^6>^5=^7<P2P9%C8R<g02>`R=%G5R>AF:<1RA3DR@7J9R310:1RB,I5RC10<@,4<RD,191094RE10:5RF'9RG!s>#H,A9,09,22X!tL#95RI/9BRJ!sB#K,19%G4R4!t-#55D=,0<,4<,19/!sU$P0P0%[9R=P=PDPKP0\0/@=10<>R=%<6#<!s$$?,A<9Y<ARA,0<R6'9,1<14<2/2H!sj#B10<4/92,1!t&#!s;%11<IR4192F!s<094BRD,4<12!sa%<PDPJ%?7R7/=BRH,84RL11<2RM11<G'!uH$8IHRG11<E1=7FRF'8,1</2MX00%?8R8,=7RM,7L18E!t:#RN!v#&7IM182F/7M/2N!s7$GM17EM/8!s:%!uu$IPHPM1W78g00=oRH/>7RF1;H81>HM[RE[1;H7RNg00RoROAV781UW31;HM\O^3NP1g00SK1UH7'@PFeO1PEg00T1RE#T%NE%L0%K0%M0R!s=#Q0RF!s,#ORNP!sy#QoROPEPFPNPNPOP01E07=O0<g00kg1E0HCP!tG#OFQER1SEOP2P5!{@#lROg00:6RE'@1i25=:OEdAh0H1Cgb9b;b<A:0MHg02^<[P2b8b4b:b4Cf!vr#%BGD3P4%BID311<L%BLD3PJP?10:2R:,;HR?1>:81;HB%c2P1!{:7X1;P?^1;!t`#O1b2R29HIBD3PDAH4B2D3Cb11<!xW$]<DD3P=%\5D3P6%^1D3A_<>!y`#A`<>AD3Ga1A9K,091Z9KD31093R3%d@!s1$C,23eO4b2W1W=o"). Qed.

Lemma w_srliw : ltac2:(zQ "a0!h9!jc!vd!kp9!jj4!kn4!ku6!kte!lg4!hq7>1a@1$1@1$0#k0>1s@1$1@1$0#5@3$2@1$1@1$0#k0@3$4@1$0#i0@1$0#k0@3$6$3@1$7^2@3$5@1$0#5@1$0#i0^1@2$8^2@2$9@1$0#5^1").
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01zh12b1h22b2h31nh41Hh51ah61sp;1p;3p;2p;6p;8g001:j14Tg002Dj1:Tg002bj12Tg001_j15Tg009>j39Tg007Ej20Tg017lj3ETg02LSj1=Tg025Mj3>Tg02RSj3<Tg0199j3ATg02^Yj2@Tg00k@j23Tg00fdj26j1LTg00cgj28Tg01;Qj2;Tg003mj2?Tg005Lj1KTg01\hj3JTg02QDj1ITg000\j67Tg02]0j1DTg02AHj3FTg02B0j3CTg00iUj8GTg01=kj2HTg02Vgj1BTg006gR0f1R1f0R239p=1g004GR3#4R4#4#4#4#4R5#4#:R6#2%54#:R4#2g009XR7%22R8%21R9g00;Nf2R:#2?912f3R;/0:10;1'1R<[10:110:2'1%2;?9:1[R=f4#2?9;:\<AE:12P2n2001000000120000000W2W1W3P=^29^18^37P2P6%:5R5g02BaR7%=:R8A>451R93<R=7A6R<1041R>,@:R?P0105=,35R@,66106;,65104:RA'8,35RB,;6,06,12X00P0106:,65RC/8>,35RD,66%=;R;A>45:5<7,05,35,66/12X00P0P0%L6R7P7P@PDP0\0/?7P01058R7%53#5#5#5#K,;59J59R9,05R3'81352/1BX00P0P>105;/82,35/1BX00P0PC182A,35/1BX001?0DP7%I:E7P3%D1E7AF589,05AC589E7GG1;6D,061H6DE7106<R<%B=E7106?,1<eO4b4W6W5o"). Qed.

Lemma w_sraiw : ltac2:(zQ "a0!h9!jc!vd!kqe!jj4!kn4!ku6!kte!lgf!hq7>1a@1$1@1$0#k0>1s@1$1@1$0#5@3$2@1$1@1$0#k0@3$4@1$0#i0@1$0#k0@3$6$3@1$7^2@3$5@1$0#5@1$0#i0^1@2$8^2@2$9@1$0#5^1").
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01zh12b1h22b2h31nh41Hh51ah61sp;1p;3p;2p;8p;6g001:j15Tg002Dj1:Tg002bj14Tg001_j18Tg009>j39Tg007Ej20Tg017lj3JTg02LSj1=Tg025Mj3?Tg02RSj3<Tg0199j3BTg02_aj2ATg00k@j21Tg00fdj23j1OTg00cgj27Tg01;Qj2;Tg003mj2@Tg01:ij2>Tg005Lj1NTg01\hj3MTg02UXj2ITg02`ij1HTg02]0j1ETg02DTj3FTg02E=j3GTg00iUj8DTg01=kj2KTg02Vgj1LTg000\j6CTg006gR0f1R1f0R239p=2P0f4R3f3R4f2R5P1P2ECp=6g004GR6#5R7#5#5#5#5R8#5#:R9#4%87#:R7#4g009XR:%42R;%41R<g00;N%45?91210451041'2R=[10511052'2%44?951[R>%43?945\=AJ512P2n2001000000120000000W2W1W3P>^2<^1;^3:P2P9%:8R8g02EoR:%=5R;A?781R<3<R>7B9R=1071R3,A5R?108>,18R@,391094,181075RA'7,18RB,;9,09,22X001095,18RC/73RD,18RE,39%=4R4A?7855<:,08,18,39/22X00P0P0%O9R:P:P@PEP0\0/@:1>8;R:%86#8#8#8#N,;89M8<R<,08R6'7,381182/2BX00P31>84/72,38,18/2BX00PC172A,38,18/2BX00PE122BX001@0E138D,181I8DD6P:%H5D6P6%E1D6AF8;<,08AG8;<D6GD1;9E,091K9ED6109=R=%L>D6109?,2=eO4b4W6W5o"). Qed.

Lemma w_addw : ltac2:(zQ "80!h9!jc!kte!vd!jv3!jj4!ku6!lha>1a@1$1@1$0#k0>1b@1$1@1$0#k0@3$3@1$1@1$0#k0@3$5@1$0#i0@1$0#k0@3$6$4@1$2^2@1$2^1@2$7^2^1").
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01zh12b1h22b2h31nh41Hh51ah61bp;1p;3p;2p;8p;6g001:j16Tg002Dj1>Tg002bj17Tg009>j38Tg007Ej20Tg017lj3ITg02LSj19Tg02RSj3:Tg0199j3@Tg02b6j2?Tg00k@j22Tg00fdj21j1KTg00gJj25Tg01;Qj2=Tg003mj2;Tg02TCj3JTg00m0j3HTg02UXj2ETg02QDj1<Tg013dj3CTg01Toj3BTg00iUj8DTg01=kj2ATg02Vgj1FTg000\j6GTg006gR0f1R1f0R238p=3P0f4R3f3R4f2R5P1P2EGp=4g004G#6#6#6#6#6R6#6#>R7#7R8g009XR9%72R:%71R;g00;N%75?81210451041'3R<[10511052'3%74?851[R=%73?845\<AI512P2n2001000000120000000W2W1W3P=^2;^1:^39P2P7%>6R6g02X7R9%95R:%91R;3:R=7@7R<1?51R3106=,26R>,171074R?1075R@'5,26RA,=7,07,32X001071RB,5@,26RC,17%94=:9:,06,26,17/32X00P0P0%K7R9P9P>PCP0\0/;9106:R9106;R>'5,161262/3AX00116@R41529,16,26/3AX00116BRD116?/52,16,26/3AX00154DR4,26R?132AX00RA15@D,26R2PAPCPA1;0CP2AJ6@BD4P?AH6@DD41164,261E64D4P>%<1D4P9%<5D4AC6:;,06AB6:;D4GD1=7C,071A7CD4107<R<%F=D41073,3<eO4b4X68W5o"). Qed.

Lemma w_subw : ltac2:(zQ "80!h9!jc!kte!vd!kg7!jj4!ku6!li4>1a@1$1@1$0#k0>1b@1$1@1$0#k0@3$3@1$1@1$0#k0@3$5@1$0#i0@1$0#k0@3$6$4@1$2^2@1$2^1@2$7^2^1").
Proof.
ltac2:(KReplay.run1z (kr_t_PropExec ()) ["WithFP1"] "##2Rh01zh12b1h22b2h31nh41Hh51ah61bp;1p;3p;2p;4p;8p;6g001:j18Tg002Dj1A!s/$bj17!s/#9>j39!s/#7Ej20Tg017lj3NTg02LSj1;!s/#RSj3?!sA#99j3D!s8#c=j2C!s\#k@j26!s/#fdj23j1P!s2#hUj25!sV#;Qj2@!s8#3mj2=!s/#5Lj1>!s/$jj2O!s/#6Gj24!sz#dDj3M!s/$lj3G!s/#P6j1:!s/#[aj4F!s/#UXj2E!s/#QDj1<!s/#eTj3H!s/#f9j3I!sw#iUj8J!tL#=kj2K!sA#Vgj1B!sA#0\j6L!tC$gR0f1R1f0R239p=1P0f4R3f3R4f2R5P1P2ELp=2g004G#8R6#8!s$%R7#8#AR8#7R9!v\#XR:%72R;%71R<g00;N%75?91210451041'1R=[10511052'1%74?951[R>%73?945\=AN512P2n20010!s#$12!s-%0W2W1W3P>^2<^1;^3:P2P8%A7R:!ug#gR;%;5R<%;1R>3?R=7D8R31C51R?10:=,6:R@,381084RA1085RB'5RC!s>#D,@8,08,12X!tE#81RE,5BRF!sB#G,38%;4=?;<,0:,6:,38/!sO$P0P0%P8R;P;P@PGP0\0/=;10:<R!s+#>R@'5,3:16:2/1D!t$#3:BR4152;,3!sp#!s<+ERH13:A/52!s?054HRI,6:112!s6#P:PIPF%>6%>7'OR7,4I13:CR6!u-&4B7RD1524/47/16!s9$E7RJ14A7R!t'#!s>-F7R615AD!s9$!sd$5BJ/47RA14C7!sw%R2P6P21=06PAAMBE7D215D!sL#AGBJ!s4#3:F%:FD2PH%:ED2P4%:B!s=$IRB%:ID2CF16:B1E!s2#P@%<1D2P;%<5D2AH:<>,0:AI:<>D2GJ1@8G,081K8GD21083R3%B=!s1$?,13eO4b4X69W5o"). Qed.

Lemma w_sllw : ltac2:(zQ "80!h9!jc!kte!vd!ko4!jj4!ku6!lie>1a@1$1@1$0#k0>1b@1$1@1$0#k0@3$3@1$1@1$0#k0@3$5@1$0#i0@1$0#k0@3$6$4@1$2^2@1$2^1@2$7^2^1").
Proof.
ltac2:(KReplay.run1z (kr_t_PropExec ()) ["WithFP1"] "##<ch01zh17__arithh24__ffh38__varmaph45__with51Hh62Hah74__p1h86__sat0h9!s/%1h:4__x1h;2b1h<2b2h=1nh>!sD%2h?1ah@1bp;1p;3p;2p;4p;6p;7p;8g001:j18Tg002Dj1J!s/$bj1;!s/#9>j39!s/#7Ej20Tg017lj3ZTg02LSj1@!s/#RSj3H!sA#99j3R!s8#gSj2O!s\#k@j25!s/#fdj21j1\!s2#5Lj1F!s/#6Gj24!s_#AXj27!s/#;Qj2C!sA#3mj2A!s/#1_j1=!sA#\hj3X!s8#B2j1W!s/$Rj1V!s/#IDj1U!s/#CPj1T!s/$nj1S!s/#DYj2D!s/#Jcj4E!s/#Fej2Q!s/#GGj2P!s/#H3j3N!s/$Rj4M!s/#;2j2<!u?#J5j3L!s8$NR0j2G!u5$jj2?!s/#b9j2:!sL$\j2K!s8#@Ej2r!s/$mj3q!s/#AQj2p!tN$@j3o!sS#Ykj6n!s/#ZOj4e!s/#P6j1B!u+$2j2b!s/#E<j2^!s/#N]j6]!s/#OAj7_!sA$_j1`!s8$ej8a!se#[8j3I!s/$aj4[!s/#UXj2c!s/#QDj1d!s/#hZj1Y!s/#=Gj3f!s/$oj3g!sn#iUj8h!w##=kj2i!sA#Vgj1j!tL$9j7k!s/#:Vj2l!s/#0\j6m!x%$gR1f1R2f0R339p=2P2g00Q0R4!s,#OR5P5!s/#oR6P3g00ROFkp=>g00=oR7/l3p=6P1f4R8f3R9f2R:P2P3Emp=!sT#4GR;#8R<#8!s$%R=#8#JR>#;R?!zR#XR@%;3RA%;2RBP0%;:?923109:1092'2R0[10:210:3'2%;9?9:2[RC%;8?99:\0AZ:23P3n20010!s#$12!s-%0W<W;W=PC^<B^;A^=@P3P>%J=R@g02>`RA%@:RB%@2RC3HR07R>RD1O:2RE10@0,5@RF,1>10>9RG10>:RH%F=R='4RI'7RJ!sG#K,C>,0>,23X0110>2RL/4=RM,7HRN!sG#O,1>%@9RP=HAB,0@,5@,1>/!sV$P1P1%\>RAPAPFPOP1\1/AA10@BRA%=;#=!s$$F,C@9X@CRC,0@RF'7,1@15@3/2K!sj#M10@P/73,1!t&#!s;%11@HRP173I!s<07PMRP,5@123!sa$@PPPNg00T1RN#WRK%VNRN%U1RQ%T1RR%S1RSP11D17!~g#0T]1D1=CE'>1QS6RUP3P:!xO#lRV!ym#6RW'A1P3:=9VWdAN172CMRWb2b3b41<7=P3b19LL=%6M1<M='G11@GRM%F<R</?IRL':RV11@3RX10>8R814G=RY!ug$'2!u7#:GLRZ11@81?<YRY':,1@/2X!sA#?<=RX,4V1:8Y,1@R[!wY&4GX1:3Y/4X/2[!s7$ZX148X/:!s:%!wN$GPLPX1KH=RL%6H%6=RH148=R8#6[[RY1r<=1<7<R[1<7X\HRH[%6<R\!{r#oR]Aq<=2UW6%6X\]^6\!|L$SK1p7<'AP[eO1PHPKPNPQPRPSP4P5P5P6!vw$<=o1@g00kgPTCE,>SEnPUP!vR&A91X7g02^<[!vY#b9b8b9b>Ce11@Z%BZD3PM%BGD311@V%BVD3PJPLPYp-0RY!t?#1b12!tA0!tK-!#6'#PI1^1;!tG$R;!sD-9E]F_%`5P;Ga!t^,X:1W7%63/G2%62[^:1^7YP31<8=P8P:O!tr#8R89IGID317MIAIMI8D3b5C[11@!z8$c@PD3PA%d:D3PF%Y2D3Af@B!{A#Ag@BCD3Gh1C>O,0>1i>OD310>DRD%j0!s1$E,2DeO4b5X@?W?o"). Qed.

Lemma w_srlw : ltac2:(zQ "80!h9!jc!kte!vd!kp9!jj4!ku6!lj8>1a@1$1@1$0#k0>1b@1$1@1$0#k0@3$3@1$1@1$0#k0@3$5@1$0#i0@1$0#k0@3$6$4@1$2^2@1$2^1@2$7^2^1").
Proof.
ltac2:(KReplay.run1z (kr_t_PropExec ()) ["WithFP1"] "##/}h01zh12b1h22b2h31nh41Hh51ah61bp;1p;3p;2p;6p;8g001:j13Tg002Dj1>!s/$bj14!s/#9>j38!s/#7Ej20Tg017lj3KTg02LSj1;!s/#RSj3=!sA#99j3B!s8#ihj2A!s\#k@j22!s/#fdj27j1L!s2#5Lj1@!s/#6Gj2?!s/#cgj26!sh#;Qj2:!s8#3mj2<!s/#1_j19!sA#\hj3J!t'#QDj1I!sA#0\j65!s8#hZj1E!s/#AHj3D!s/#B0j3C!sJ#iUj8F!se#=kj2G!sA#Vgj1H!tL$gR0f1R1f0R238p=1g004GR3#!s$+R4#3#>R5#4R6!v&#XR7%42R8%41R9g00;Nf2R:#4?812f3R;/0:10;1'1R<[10:110:2'1%4;?8:1[R=f4!sR#;:\<AK:12P2n20010!s#$12!s-%0W2W1W3P=^29^18^37P2P5%>4R7!uN#aR8%;:R9%;1R=3=R<7B5R>1A:1R?P0107<,27R@,75105;,77105:RA%@4R4'?RB'6!sF#C,:5,05,12X00P0177ARA1051/?!sN#!sJ$D,75%;;R;==89,07,27,75/!sY&P0%L5R8P8P@PDP0\0/<8!tN$9R8%93#9!s$$@,:79J7=R=,07R3'61272/1C!si%4107;/62,27!s:+A162B!s7+1<0DP8%I:E5P3%E1E5AD79!ss#AC79=E5GF1:5D,051G5DE!uj#>R>%H<!s1$?,1>eO4b4X66W5o"). Qed.

Lemma w_sraw : ltac2:(zQ "80!h9!jc!kte!vd!kqe!jj4!ku6!lk2>1a@1$1@1$0#k0>1b@1$1@1$0#k0@3$3@1$1@1$0#k0@3$5@1$0#i0@1$0#k0@3$6$4@1$2^2@1$2^1@2$7^2^1").
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01zh12b1h22b2h31nh41Hh51ah61bp;1p;3p;2p;8p;6g001:j15Tg002Dj1=Tg002bj14Tg009>j38Tg007Ej20Tg017lj3NTg02LSj1:Tg02RSj3?Tg0199j3DTg02joj2CTg00k@j21Tg00fdj23j1OTg005Lj1ATg006Gj2@Tg00cgj27Tg01;Qj2;Tg003mj2>Tg01:ij2<Tg001_j19Tg01\hj3MTg02UXj2GTg02`ij1FTg02hZj1ETg02DTj3HTg02E=j3ITg00iUj8JTg01=kj2KTg02Vgj1LTg000\j6BTg006gR0f1R1f0R238p=2P0f4R3f3R4f2R5P1P2EBp=6g004GR6#5#5#5#5#5R7#5#=R8#4R9g009XR:%42R;%41R<g00;N%45?81210451041'2R=[10511052'2%44?851[R>%43?845\=AN512P2n2001000000120000000W2W1W3P>^2<^1;^3:P2P8%=7R:g02EoR;%:5R<%:1R>3?R=7D8R31C51R?10:=,1:R@,381084,1:1085RA%A7R7'@RB'7,1:RC,;8,08,22X0011:ARA1081/@7R7'7RD,1:RE,38%:4R4=?;<,0:,1:,38/22X00P0P0%O8R;P;P@PEP0\0/>;1<:<R;%96#9#9#9#A,;:9M:>R>,0:R6'7,3:11:2/2CX00P71<:4/72,3:,1:/2CX00PA172B,3:,1:/2CX00PE122CX001>0E13:D,1:1G:DD6P;%F5D6P6%E1D6AH:<>,0:AI:<>D6GJ1;8E,081K8ED61083R3%L=D6108?,23eO4b4X69W5o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma m_mul : ltac2:(zQ "60!h9!jc!vd!lkc!ll5!llf>1a@1$1@1$0#k0>1b@1$1@1$0#k0@3$2@1$1@1$0#k0@4$4@1$0#k0$3^2^1@2$5^2^1").
Proof.
ltac2:(KReplay.run1z (kr_t_PropExec ()) ["WithFP1"] "##$0h01ah11bp;1p;2g001:j10Tg002Dj14!s/$bj12Tg02l6j21!s8#3mj23!s/#4G#0!s$-4#2R0f1f0'1,30X10W0o"). Qed.

Lemma m_mulh : ltac2:(zQ "60!h9!jc!vd!lm8!ll5!ln2>1a@1$1@1$0#k0>1b@1$1@1$0#k0@3$2@1$1@1$0#k0@4$4@1$0#k0$3^2^1@2$5^2^1").
Proof.
ltac2:(KReplay.run1z (kr_t_PropExec ()) ["WithFP1"] "##$0h01ah11bp;1p;2g001:j10Tg002Dj14!s/$bj12Tg02m<j21!s8#3mj23!s/#4G#0!s$-4#2R0f1f0'1,30X10W0o"). Qed.

Lemma m_mulhsu : ltac2:(zQ "60!h9!jc!vd!lnc!ll5!lo8>1a@1$1@1$0#k0>1b@1$1@1$0#k0@3$2@1$1@1$0#k0@4$4@1$0#k0$3^2^1@2$5^2^1").
Proof.
ltac2:(KReplay.run1z (kr_t_PropExec ()) ["WithFP1"] "##$0h01ah11bp;1p;2g001:j10Tg002Dj14!s/$bj12Tg02nCj21!s8#3mj23!s/#4G#0!s$-4#2R0f1f0'1,30X10W0o"). Qed.

Lemma m_mulhu : ltac2:(zQ "60!h9!jc!vd!lp4!ll5!lpf>1a@1$1@1$0#k0>1b@1$1@1$0#k0@3$2@1$1@1$0#k0@4$4@1$0#k0$3^2^1@2$5^2^1").
Proof.
ltac2:(KReplay.run1z (kr_t_PropExec ()) ["WithFP1"] "##$0h01ah11bp;1p;2g001:j10Tg002Dj14!s/$bj12Tg02oLj21!s8#3mj23!s/#4G#0!s$-4#2R0f1f0'1,30X10W0o"). Qed.

Lemma m_div : ltac2:(zQ "60!h9!jc!vd!lqa!ll5!lr3>1a@1$1@1$0#k0>1b@1$1@1$0#k0@3$2@1$1@1$0#k0@4$4@1$0#k0$3^2^1@2$5^2^1").
Proof.
ltac2:(KReplay.run1z (kr_t_PropExec ()) ["WithFP1"] "##$0h01ah11bp;1p;2g001:j10Tg002Dj14!s/$bj12Tg030Tj21!s8#3mj23!s/#4G#0!s$-4#2R0f1f0'1,30X10W0o"). Qed.

Lemma m_rem : ltac2:(zQ "60!h9!jc!vd!lrc!ll5!ls5>1a@1$1@1$0#k0>1b@1$1@1$0#k0@3$2@1$1@1$0#k0@4$4@1$0#k0$3^2^1@2$5^2^1").
Proof.
ltac2:(KReplay.run1z (kr_t_PropExec ()) ["WithFP1"] "##$0h01ah11bp;1p;2g001:j10Tg002Dj14!s/$bj12Tg031Zj21!s8#3mj23!s/#4G#0!s$-4#2R0f1f0'1,30X10W0o"). Qed.

Lemma w_mulw : ltac2:(zQ "80!h9!jc!kte!vd!lkc!jj4!ll5!lse>1a@1$1@1$0#k0>1b@1$1@1$0#k0@3$3@1$1@1$0#k0@3$5@1$0#i0@1$0#k0@4$6@1$0#i0$4@1$2^2@1$2^1@2$7^2^1").
Proof.
ltac2:(KReplay.run1z (kr_t_PropExec ()) ["WithFP1"] "##7~h01zh12Hah26__sat1h32b1h42b2h51nh61Hh77__arithh84__ffh9!sR%0h:8__varmaph;5__with<1ah=1bp;1p;3p;2p;4p;7p;6p;8g001:j19Tg002Dj1C!s/$bj17!s/#9>j38!s/#7Ej20Tg017lj3XTg02LSj1<Tg032`j4?!sA#99j3K!s8#3Jj2H!s\#k@j26!s/#fdj23j1`!s2#b9j25!sV#;Qj2D!s8#3mj2:!s/#5Lj1A!s/$jj2Y!s/#6Gj24!s/#@Ej2W!s/#;2j2@!s/#:Vj2=!sA$mj3V!s/#AQj2U!s/#B2j1R!s/$Rj1Q!s/#IDj1N!s/#CPj1J!s/$nj1I!s/#DYj2>!s/#J@j3G!s/$cj4L!s/#N9j7M!uc#Ykj6F!s8#Fej2O!s/#GGj2P!s/#H3j3E!s/$Rj4S!uu#4Qj4T!s\#ZOj4c!s/#P6j1;!s/#[aj4b!s/#UXj2a!s/#QDj1B!s\#5:j3_!s/$_j3]!sw#iUj8\!vG#=kj2[!sS#Vgj1Z!sA#0\j6^!v>$gR0f1R1f0R238p=1P0f4R3f3R4f2R5P1P2E^p=2g004G#9R6#9!s$%R7#9#CR8#7R9!xW#XR:%72R;%71R<!w,#N%75?81210451041'1R=[10511052'1%74?851[R>%73?845\=AX512P2n20010!s#$12!s-%0W4W3W5P>^4<^3;^5:P2P8%C7R:P:g036MR;%<5R<%<1R>C?R=7K8R31H51R?10:=,6:R@,381084RA1085RB'5RC!s>#D,D8,08,12X!tG#81RE,5BRF!sB#G,38P:P;%<4P<C?,0:,6:,38/!sS$P0P0%`8R4P4P@PGP0\0/:410:<R!s+#>R@'5,3:16:2/1D!t+#3:BR;1524,3!sp#!s<+ERH13:A/52!s?05;HRI,6:112!s6#P:PIPF%A6R6%A7R7'YRD,4I13:CRJ!u6&4BDRK152;/4D/1J!s9$EDRL14ADR!t/#!s>-FDRJ15AK!s9$!sd$5BL/4DRA14CD!sw%RCPJPC1:0JPAPBPEPD1W67g00=oRA/@6RJ1=A71@AD[RC[1=A6RMg00RoRNAV671UW11=AD\N^1MP1g00SK1UA6':PJeO1PCg00T1RC#R%QC%N0%J0%I0R!s=#Q0RJ!s,#ORMP!sy#QoRNP!t\#MPMPNP01>06=G0:g00kg1>0ACL!tG#OFMEF1OCNP2P5!zu#lRN!~L#6RC':1P25=8NCdAE0A1CSb8b:b;A80DAg02^<[P2b7b2b9b2R2CTD215K!v0#PBPLPDP2CcD213:F%;FD2PH%;ED2P;%;B!s=$IRB%;ID2Cb16:B1a:ID2P@%B1D2P4%B5D2A_:<>,0:A]:<>D2G\1D8G,081[8GD21083R3%Z=!s1$?,13eO4b6X=9W<o"). Qed.

(* [comment removed for export] *)
Lemma div0_32 : ltac2:(zQ "80!h9!il1!hq7!o7!vd!kte!jc!hj6>1b@1$6@1$0#k0@3$4$3@2$1@2$2@1$0#i0@1$5^1Z@2$1@2$7@1$0#i0@2$2@1$0#k0^1Z").
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01bh11zp;1p;2p;3p;6g001:j10Tg002Dj13Tg002bj19Tg007Ej21Tg00fdj24Tg0379j22Tg009>j3:Tg003mj28Tg02LSj17Tg02QDj16Tg000\j65Tg004G#0#0#0#0#0R0#0#3R1#9g006gR2%30R0f0R3,11'4R4g004lR5g00=oR6,23f1,11,40/263:X121246,85%73,10%63E5W0o"). Qed.

Lemma w_divw : ltac2:(zQ "80!h9!jc!kte!vd!lqa!jj4!ll5!lt8>1a@1$1@1$0#k0>1b@1$1@1$0#k0@3$3@1$1@1$0#k0@3$5@1$0#i0@1$0#k0@4$6@1$0#i0$4@1$2^2@1$2^1@2$7^2^1").
Proof.
ltac2:(KReplay.run1z (kr_t_PropExec ()) ["WithFP1"] "##32p'0h01zh11Hh21bi001bh32b1h42b2h51nh61ah72b0i014div0p;1p;2p;3p;8p;6p;4g001:j18Tg002Dj1B!s/$bj13!s/#7Ej20!s/#fdj26j1LTg0379j2=!s/$Vj1KTg01;Qj2:Tg02LSj1;!sA#84j3<!sA#99j39!sh#k@j21!sA$[j27!s8#9>j34!sJ#7lj3M!s8#3mj2>!s8#:ij2A!sw#`ij1?!s/#UXj2J!se#!sw#G!sS#iUj8F!sS#=kj2E!sJ#Vgj1D!sJ$ij1H!sJ#0\j6@!s8#2`j4C!s/#;1j2I!sA#6gR0f1R1f0R234p=2P0f4R3f3R4f2R5P1P2E@p=5g004GR6#8!s$'R7#8#BR8#3R9!sC#lR:%B7R71082'6g00=oR;'=R<P:%37R=P2%K6R6,:7R>%;5R?%;1R@5<7n01101000200009978P:P91081RA,67/=;1:86R61085,17RB117A'7,17,:8n!s`$!sc'549X2:P<P:!s$$=P2P>%;4R==<7?R<!t89P2P!t&#4!t&#:/7B!s-#A,:8RC!t'4P2!wv#XRD%32RE%31RFg00;N%35?41210451041'2RG[10511052'2%34?451[RH%33?445\GAM512P2n20!t1'1!t2$000W4W3W5RGPH^4F^3E^5DRDP2P8A978>!ty$6,>0O4b1PGP!s@+<RDPC107<RG!u7#6,681083!s2#>/7:!s-#E,:8,08,22X00168A%;3=<7=,0!vk$68/!s@$P0P0%L8R3P3P6PAP0\0/>31A7=R!s+#?R6'7RF,67RH1172/2E!su#17F12!s1$P:172!tG#!s@%PB17>2!s5+1>0AP6%?5D5P3%?4D5117H1J7FD5PGAG7=?D5GF108C1E8AD5108D%D<D5!uh#!x0$!wX'1b7%;2R<,0!y;#%H2E@P7g03<8P@P<CC!xO#1I12549eX29W6o"). Qed.

Lemma w_remw : ltac2:(zQ "80!h9!jc!kte!vd!lrc!jj4!ll5!lu2>1a@1$1@1$0#k0>1b@1$1@1$0#k0@3$3@1$1@1$0#k0@3$5@1$0#i0@1$0#k0@4$6@1$0#i0$4@1$2^2@1$2^1@2$7^2^1").
Proof.
ltac2:(KReplay.run1z (kr_t_PropExec ()) ["WithFP1"] "##4Ip'0h01zh11Hh21bi001bh32b1h42b2h51nh61ah72b0i014div0p;1p;2p;3p;8p;6p;4g001:j19Tg002Dj1E!s/$bj16!s/#7Ej20!s/#fdj22j1KTg0379j2=Tg02LSj1;!s8#<dj3<Tg0199j3:!sV#k@j21!s8#;Qj27!sJ#=Jj28!sA#9>j35!sA#7lj3M!s8#3mj2>!sw#UXj2C!s/#QDj1L!sJ#=kj2B!s8#Vgj1A!s8#:ij2@!s8#`ij1?!t$$gj3I!sn#iUj8H!s8#9ij1G!s8#0\j6D!s8#2`j4F!s/#>Vj2J!sA#6gR0f1R1f0R235p=3P0f4R3f3R4f2R5P1P2EDp=!v?#4G#9!s$'R6#9#ER7#6R8!sA#lR9%E6R61072'2g00=oR:'=R;P9%66R<P2%;5R=%;1R>9<6=n01101000200009:67P9P81071R?,26/=:1075,16R@,77116?,8@,16,77n!s^$!sa'558X29P;P9!s$$!t7$4R<A<6<=R;!t59P21074R9!t,#?,77RA18?!t+#RB!s4#C!t04P!uH#9XRD%62RE%61RFg00;N%65?51210451041'3RG[10511052'3%64?551[RH%63?545\GAM512P2n20!t1'1!t2$000W4W3W5RGPH^4F^3E^5DRDP2P7A:67<REPA106<RF!u{#271073!u##H,77,07,32X!sr#7?RI%;3R3,06!sO%/!s@&69RJ1162RK!sd#27HRL'3X00P?1272/3L!sL#>0I116J1C69D4PF%L4D4107A1B7?!s0$E%A<D4O4b1PGP!tl+;RDPC106;RG!tb#E!t0#8H?!s2#A!tn2BA<63<!tl2P0P0%K7R3P3PEPBP0\0/>31@6<R!s+#=RE'8RF,26R913KA!sp#16F132!s1#P?182!v&#/3!s5$@18H2!s5+1>0BPE%?5D4P3%?!uF#1691C6FD4PGAI6<=D4GH107C1B7B!u[$D%A;!u[%!yU$!xw%101b7%;2R;,0!z]#%G2EDP6g03?]P>P;CF!yt#1J12558eX28W6o"). Qed.

Lemma w_divuw : ltac2:(zQ "80!h9!jc!kte!vd!luc!jj4!ll5!lv6>1a@1$1@1$0#k0>1b@1$1@1$0#k0@3$3@1$1@1$0#k0@3$5@1$0#i0@1$0#k0@4$6@1$0#i0$4@1$2^2@1$2^1@2$7^2^1").
Proof.
ltac2:(KReplay.run1z (kr_t_PropExec ()) ["WithFP1"] "##0op'0h01Hh11bi001bh22b1h32b2h41nh51zh61ah72b0i014div0p;1p;2p;3p;6p;4g001:j14Tg002Dj1>!s/$bj13!s/#7Ej20!s/#fdj22Tg0379j2<!s/$Vj1?Tg01;Qj27Tg02LSj16!sA#@Ij3:!sA#99j35!se#Zcj29!s/#k@j28!s/#9>j31!sJ#7lj3E!s8#3mj2=!s8#=kj2D!s8#0\j6;!t$#Vgj1C!t$#9ij1@!s/#2`j4A!t:$oj2B!sS#4GR0#4!s$'R1#4#>R2#3R3!sC#lR4%>1R1f0R5,02'2g00=oR6'<R7P4%31R8P5%?0R0,71R9f2R:#6R;f1R<#6R=5:1n01101000200009512P4P3102<,21R>/<61720R0102:!s8#?/9>,81,72n!s]$!s`'513X14P7P4!s$$8P5P9f3R8#6R7=:1;R;!t89P5P!t&#8!t&#4/9?,81R?,72R>!t-4P5!w##XR@%35RA%3<RBg00;N%3:?1<!sC#6gRC108:108<31RD[10:<10:551C%38?1:<[REf4RF#3?18:\DAE:<5P5n20!t<'1!t=$000W3W2W4R:PE^3B^2A^4@R@P5P2A5129!u+$0,=CO4b0P:P!s@+;R@P>PC101;!vF#22102F,21/94!vV%,0291C5X5CPC122?R4%6F=:17,01!sX%=!sE%1=C4102>1D2?E;102@%C;E;!t?#!vj$!v:'1b7%65R;,01/<6%@5E;P1g03B7P=P;CA!w1#1B<5513eX13W6o"). Qed.

Lemma w_remuw : ltac2:(zQ "80!h9!jc!kte!vd!mg1!jj4!ll5!mgb>1a@1$1@1$0#k0>1b@1$1@1$0#k0@3$3@1$1@1$0#k0@3$5@1$0#i0@1$0#k0@4$6@1$0#i0$4@1$2^2@1$2^1@2$7^2^1").
Proof.
ltac2:(KReplay.run1z (kr_t_PropExec ()) ["WithFP1"] "##2Sp'0h01zh11Hh21bi001bh32b1h42b2h51nh61ah72b0i014div0p;1p;2p;3p;6p;4g001:j18Tg002Dj1B!s/$bj15!s/#7Ej20!s/#fdj21Tg0379j2<Tg02LSj1:!s8#Bcj3=Tg0199j39!sS#k@j22!s8#;Qj26!s8#6Gj2;!s/#9>j34!sA#7lj3H!s8#3mj2A!sw#UXj2G!s/#QDj1F!sJ#=kj2?!s8#Vgj1>!t:#9ij1E!s\#0\j6@!s8#2`j4D!s/#CIj2C!t:$gR0f1R1f0R234p=3P0f4R3f3R4f2R5P1P2E@p=7g004G#8!s$'R6#8#BR7#5R8!sA#lR9%B6R61072'1g00=oR:'<R;P9%56R<P2%:5R=%:1R>9=6=n01101000200009967P9P81071,16R?/<:1075R@,26,67116@R@/;?!s5%n!s`$!sc'548X29P;P9!s$$!t9$4R<A=6<=R!t7:P21074R9,26R;,67R?1169RA/;!t@#R@!s9#B!t54P2!wZ#XRC%52RD%51REg00;N%55?41210451041'3RF[10511052'3%54?451[RG%53?445\FAH512P2n20!t1'1!t2$000W4W3W5R5PG^4E^3D^5CRCP2P7A967<RDP?106<RE!v$#171073RG!u%#F,67,07,32X00117;RH%:3R3,06!sQ%/!s@$PA1262!s`#17FRF'3!s:#;1172/3F!s`#A0H126A1G69D7PE%F4D!t4#?1?7;!s0$D%><D7O4b1P5P!th+=RCPB106=!tf&16G/;A!wu%!te/@RAA=63<!te21A0A107B1?7@!t4$C%>=!t4%!x/$!wL%101b7%:2R=,06/<:%E2E@P6g03DQP>P=CD!xN#1C12548eX28W6o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma bv_swrap_hi : ltac2:(zQ "b0!vd!hp8!hga!mh6!mi3!jj0!hk0!hl4!hr5!mi9!hod>1n$1>1z$2>0@1$4@3$0$1^2$5>0@2$6@1$9^3^2>0@2$7^3@1$3^4@3$0$2@2$a^5^4@2$8^4@1$3^5").
Proof.
ltac2:(KReplay.run1z (kr_t_PropExec ()) ["WithFP1"] "##8,h04__x1h1!s,#2h2!s,#3h37__arithh44__ffh58__varmaph65__with71zh81Hh93Hhih:3Hloh;2Hnh<4Hposh=3Htwh>1np;3p;1p;2p;4p;7p;6p;8g009>j3@Tg03E=j1hTg00ggj16!s/#:Vj2<Tg01Bkj14!s8#;2j27!sS$Vj2X!sS$Jj21!s8#FJj1R!s8#B2j1L!s/$Rj1K!s/#C2j2E!s/#VEj4g!s8$Pj1e!s/$nj1_!s/#E<j2B!s/#1:j1Z!s/#i2j3A!s8$_j1W!tU#JXj3?!s8#5Lj1V!s/#DYj2F!s/#aVj3U!s/#Fej2T!s/#3mj2S!s/#GGj2Q!s/#H3j3P!s/$Rj4M!s/#hUj20!s/#b9j2C!s/#6Gj2=!uE#7Vj1N!s8#\Jj2O!s/#^5j19!s/$Tj28!sJ#G7j3J!s8#_fj2I!tp#H`j2f!s8#`Rj3H!uN$_j1d!s/#Jcj4;!s/#OAj7^!vk$Nj2]Tg027Aj3\!s8#0\j6G!t$$`j3[!s8#jdj6`!s/#k@j2a!s/#N9j7b!tC$=j3Y!sw$ej8c!u3$gR0f1R1f0R23@p=2P0P1!sb#gP2C;p=>!s4$Q0R3!s,#OR4P4!s/#oR5P2g00ROFbp=3AY012p=5!sc&T]!sc%Df3R6P3P4P4P5f2R7P1P2Gcp=:!y[#XR8g01@=9@81#h%67/<1%46,77f4R8/X7%68R9/19%48R9'2f5R:#Rg00=oR;%4:'7!t9#1R<#LR=%K<R>P01E07P11E06CgR?%e0R@%_0RAg004GRB,B0RC%Z!s-$D5A0RE%W!s3$F5?0RG%VBRH,F0=U0F5A0/>E'31TA5REP2P!t<#4lRI!{K#6RJ'S1Q27=@IJdAP0;1CMRJb4b5b6X00X10X201121RI/07RK1CH7'1/2I^00^10^20P2f7RI#4RL%6IRMf6RNO3b3%6N,1:RO%4NRP'01CHP!s^#OP011NMRM/0LRO1CHL'1RPf8RQ#4RR,=2%6QRQ'010IRRS'2X70P01=OLRT102Q/2SX70RSP0POPSP=P>P?P@A?0GDA?0CF'>,3APEP!u840K11027'2!u--PRPQPI!t{#PT%NB,O0g00eYRB#9RT#9#9RK,80R15J0RS180TRT180BRB'5'5g00f8RU'I%9!sL$K/5S151T,5K,5B/IU'f=H<=5H<!tr%PA1F0;R@/DF,3A%d4R?PAAA0DD/>!s8#P?PA1DC!s1'P0PDg00PIRDPCC;!s<'!zA&P0P@PDPG!s?$1DG!s\#F^C:!s$%!uv77;71177/2617781<86118:/0NRJ,<;17JN'][[[[!v=4P7P6P8P:O7b39\OLEG1=PLA[OHLEGPMP2E`b8b<b=1a861069'2eW9W:W;X70W>o"). Qed.

Lemma b_lui : ltac2:(zQ "90!h9!jc!vd!jj4!mjb!ik7!u7!mk4!hpb>3imm@1$1@1$0#h4@3$2@1$1@1$0#k0@3$3@1$0#i0@1$0#k0@5$7@1$0#i0@1$0#h4@1$0#c^1@2$6@1$0#cZ@1$4@2$5@2$8@1$0#h4^1+c").
Proof.
ltac2:(KReplay.run1z (kr_t_PropExec ()) ["WithFP1"] "##RYp'0h06__sat1h1!s/%3h24__x1h32Hah47__arithh54__ffh6!sL%0h78__varmaph85__with91zh:4__p1h;!sM%5h<!s/%7h=!s/%2h>!s/%4h?!s/%6h@1HhA1xhB2H0hC2b1hD2b2hE1ni001nhF3HgehG3HlthH2HrhI1ehJ3immhK1ohL1yp%0p&0p;1p;3p;2p;5p;6p;4p;8p;7p;<g001:j1ET!s/#_j1<!s/#2Dj1C!s/$bj1F!s/#9>j3=!s/#7Ej20Tg017lj3u!s/#;Qj2TTg03HEj5X!s8#99j3k!s/#:ij2W!s\#5Lj1>!s8#AXj2B!sS$mk10!sx$k@j24!s/#fdj2Sk10!t,#03mj2:!sX#<7R0j1_!s:#UDj2Q!s:#B8j2x!s/$kj1`!sA#;2j23!s/$NR1j2?!tC$jj2@!s/#b9j26!tC#J3j2o!s8#:VR2j27!s1#?FR3j2m!s1#@Ej2G!s/$mj3H!s/#AQj2j!s/#B2j1i!s/$Rj1h!s/#C2j2g!s/$Pj1f!s/$nk10!tH$E<k20!uf#0DYj2U!s/#J@j3L!sB$_k10!w+$N]k60;!tf$Xj2e!s9#Fek20!v'$GGk20!uH$H3k302!s0$Rj4~!sV#K;j1b!s/$Xj3V!sA#^Tj2P!s/$5j1a!s/#_=j3N!s/$fj2O!vK#H`j2z!s8#[aj2y!s/#e0j3^!s/#`Rj3M!s/#aVj3]!s/#hUj2I!s\#JXj3\!u8$cj4R!tC#LEj2w!s/#E=j1Z!s8$dj5c!sJ#IDj1vTg02[8j3Y!se#E]j1t!s/#F;j4|!sS#N0j1}!sJ#8ej3r!s\#0\j6d!sA$Qk201!s0$nj6q!sB#iUj8p!sf#=kk205!s^#Vgk10!x>#0N9k70!x4$OAk708!s0$ej8n!s/#jdk609!sa#LCm<0!yc$ILl<lTf0R4#E#Ep=Ag006gR5f1R6;=4p=2g00=oR7/74p=113!s,#DP5P6g00T]P4CRp=J!s4$Q0R8!s,#OR9P9!s/#oR:P4g00ROK07p=5!s\&PI!s\%;f2R;P8P9P9P:P6P4K08p=Kf3R<!s<+;!s>#Gnp=9P5f4R=P<!s9%Edp=!t;#9XR>!s8#!}5#Pg01@=R?P4J09p=[P>P!tA#5P0P0f5R0P!sd+N<0:p={!sC$2P0P2P=P7P7!sE'M<lp=sg004GR2#ER@#<#ARA#CRB#F%F4RC%F6RDP1%F;?=6410<;10<6'2R1[10;610;4'2%F<?=;6[RE%F=?=<;\1Au;64P4n20010!s#$12!s-%0WDWCXE>PE^DD^CC^E>P4%E@RC#E#ARD#ERE#CR1%CDRFPFPB%<2RG#ARH#CRIP61TI7RJDXRK7k1S001WB6%>HRH'BRL$0=S0110FKS02,4FRM,S11WB;/BHRN,T1,01,24X951S1L!t+#PIP;PJDX,0F,4F,S1/!sE$!vP#&001ROPOPMPLP5\5/:O10B6RO%_IRM'BRP10IJS03'Q14F4RQ/2NX95RRP5P710B;RS/BMS04/Q4,4F!sD%PPPR1xB6%1O%`BS05,3O'?%>@R@/@MRO,6S10B<RR,4B/BH,2Q!t{#4BSRQ1@@HRN'616RO!sv$!tw#%<C#<RC#>RO,@@RT,oS13ST17TS'mP313R!s2#R10B=RR/6N,4F14B!s0#'2P4!sE$0B0R0/6NR3f6,0BRU!tI#6N!vF%S06P016UNRU164NRV'2!t_#:5314B0S07%>ARA,G@RW%D@RX%1A1@@ARY#D[RZ[R[%1@R\!|&#oR]AH@A6UW3RA%1Y\]^3\R^1G@OR_!v,#DT[R`\XRaAH@O6V]X3\RO%1T!sO%b!|a$SK1j7@':PXeRcO1RdP`P=P!s0#=PZp-0Re!}d#1Rf#iRg%hfRh1g56Ri%f5Rj&0?5Rk20>52R21U5@Rl%CC5L5RC'J,5kRm&0<9RnPk1U57Ro/;2,5kPk!}[+<J0;S085KkS09Pn1e5C!sJ%=KkmC9C9204k:!~k#P;!|d#lR<g00:6R9':2034;==<9dB02576C~R9b5b7b8X25W:134TR<%16/?;R8%bT/7;13;T'?[[^25^:eP4f<!we#p/3YPpf7Rqf:RrO4b4b1b0b6b0b=b19VB0D814F3S0:1G@HRs%1HS0;%DNS0<[Rt\XRuAH@H!w$&v%1N!w$%wPWP[PAP^%<G#<#<RG#>Rx,G@S0=%1x1@@xRy!xE#z\XS0>AH@x!sj%S0?%1y!sk$S0@P_PaPOPbP!wb%zPq!wf$xPZPr!s0$cPtg00eYR{,P5R|%a{S0A#a!s3#{9N5|g00f8R}'O'zR~%AE#A#A#>,y5RE=^5{=N5|/O}=Mfg5MfPhPiPjPkPmPnPkQ!w]#%CG9L5lRG,e5AL5lIRm9]52R{';,5k1J{G,5k5Kk!ww#P:P!wL,X:e%by16;NR;'713;y'?\8\<!wF+B!wF#<!wF#<f=S09f@S0B!wH$<b;!wL/b>b;b?b<9VF3D8WGP4O1!}=#%`FRR,I3Q06Q05,I01IUR/2V!~w#sPuPvPw%>DRD!|^#R%1D1@@DRU!w:#8\XRXAH@D!w}&D%1U!w}%\!w}'!w?2ZPxP8PcPtPg!vC&!v+$FR@9\5{g00kg!s6#BRl9\52=]5mCR!{U#!v0/1IVU1I4Y!#35#^25P4P<O1!uf=Q07PBP0A=>B?R0P>PeP4g02^<RVP]n01!#8Z$!#8c&XI>R]=[B4PV1wV4R;bBW@%Z0e!uH<!u@'k1;C!}-#RCPnPC!x5217T4R017T6!|H#P4PpPqO2!|51!t0EQ081J2l!t3#l5KkR2PnPl!yG5134Y,?6Rl136Y!}`+%1pPpPrO3!tD1DcD8Q0:PFP3A=>F?R?A[F]4PVP!uq&?e!xu'!to'Q0=Q0>Q0?Q!|h6!|b#cPtAMf~!u-+PCPn1;G{,5k!v6366NRN,7y\0!x9&Q09!v7$!x<:!tZ+RPXPDP!z#DQ0A,P59^5E!}Z-!tf+2Pn1J{@!tf5!vd$NU\l!v\,<!tj#B!v]$!tj:!vi#WF!|f#!#?J,2!yw$!s'$bK1BQH!u$+d!xI%%v5RZPj1U5H,;o!{T0Q0;P!~$#!t8$R^9YQH!ws#4%1M!sA$XA5RQ1764#tXL5XA51:57PMPHPQPQ%_4,:5XA>PIPH1:5HE{EsP^C|9YSMD8bH14FP/2Le1QP7%}P!t$#3!v}+d!}Z&!th#;o!te#1Jom!#4S$!to,1777Q0<'?!tu,9rI7EdQ02PBPFPIP6PJ201BI,:>EqD8Gp1T1L,012051L!tB#0,01RL&06K!s4#!#AD$LeO4b@WJo"). Qed.

Lemma b_auipc : ltac2:(zQ "a0!h9!jc!vd!jj4!ml0!ik7!u7!jq9!mk4!hpb>1p@1$1@1$0#k0>3imm@1$1@1$0#h4@3$2@1$1@1$0#k0@3$7@1$0#k0^2@3$3@1$0#i0@1$0#k0@5$8@1$0#i0@1$0#h4@1$0#c^1@2$6@1$0#cZ@2$4^2@2$5@2$9@1$0#h4^1+c").
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01zh14__x1h24__x2h32b1h42b2h51nh61Hh77__arithh84__ffh98__varmaph:5__with;1bh<3immh=1pp;1p;2p;3p;4p;7p;8p;6p;5g001:j11Tg002Dj19Tg002bj15Tg001_j1ATg01:ij2<Tg005Lj1VTg01AXj2;Tg03Hmj1?Tg013dj3:Tg03O_j2GTg009>j36Tg007Ej20Tg017lj3YTg01;Qj28Tg00gJj22Tg00fdj23j1UTg003mj2BTg00B2j1STg00BRj1RTg00C2j2QTg00IDj1NTg00VEj4MTg00CPj1LTg00Cnj1HTg00E<j2=Tg00i2j3>Tg00Jcj4ITg00N9j7JTg00Fej2KTg00GGj2FTg00H3j3ETg00HRj4OTg00iUj8DTg01T=j3PTg000\j67Tg01=kj2@Tg01Toj3CTg03HEj5TTg0199j3XTg03Pgj1WTg006gR0f1R1f0R236p=4g004GR3#1R4#1#1#1#1R5#1#9R6#5R7%A4#1#1#9R8#5P71<82%A3#1#1R9#VR:';#?f2R;=:621<81/;:R<,G;R=567X;7g009XR7%52R>%51R?g00;N%5;?612f3R@/0;10@1'4RA[10;110;2'4%5@?6;1[RBf4#5?6@;\AAY;12P2n2001000000120000000W4W3W5PB^4?^3>^57P2P6%?<9:6;R7P=P0106;R>186<R?,06RB'2,361<8;/;:R:106@R@'2RA,86,06RC,42X00P0136<RD12@2,36/4CX00P012<>RC,36136:,2@,36/42X00P012><RE,36136A,42X00P0P0%U6RAPAPEPCP0\0/BAg00T1RA#S%RAP01Q0;P1%N0CM%L0%H0RAg00Q0g00QOREPEg00QoREP01=03R31=04R45>0g00kgA>043CIg00ROFJ1KAEP2P;g004lREg00:6RA'B1F2;=6EAdg00=oRA=E01COb8b9b:X10X2012211212'4^10^20P2P:P@O2b7GD12>D,36AP6><E7186C,061@6CE7PB1@6<E7A:6;?,06AC6;?E71067106='4eO4b6%95R5P5P8%99R9P2189ADT7X6%W2E7W<W=o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
End WithFP1.

Ltac step_pipeline Hfetch Hecall Hdecode :=
  unfold RiscvSemantics.step, RiscvSemantics.step_accesses;
  cbn [ms_pc ms_pc_val mkst];
  rewrite Hfetch;
  cbv beta iota;
  unfold RiscvSemantics.drop_access_report,
    RiscvSemantics.decode_exec_accesses;
  rewrite Hecall;
  cbv beta iota;
  rewrite Hdecode;
  cbv beta iota zeta delta
    [RiscvSemantics.interp_eff_accesses
     RiscvSemantics.width_bytes RiscvSemantics.width_bytesZ
     Sem.exec Sem.load_val Sem.store_val
     Sem.rget Sem.rset Sem.with_regs Sem.with_pc Sem.with_resv
     Sem.inval_resv Sem.w0 Sem.w1
     Sem.c_regs Sem.c_fregs Sem.c_pc Sem.c_fcsr Sem.c_resv
     ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom mkst];
  rewrite ?bv_eqb0_is_x0.

Section WithFP2.
Context {fx : FPState}.

(* [comment removed for export] *)
Lemma step_opimm_gen : ltac2:(zQ "i11!h9!jc!in5!vd!o7!hga!mlb!is5!mm4!mmb!m7!mrb!hk6!ime!ms3!q2!ir3!msa!mt7!mu5!mv1!ng3!nj1!njf!nk8!q6!jj4!ju1!nl1!nl9!nm3!tb!u0&>0@1$1@1$0#k0@1$2@1$1@1$0#8>4segs@1$d$h0>4regs@2$a@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>2op$h8>2rd@1$1@1$0#5>2rs@1$1@1$0#5>3imm@1$1@1$0#c>0@3$3@1$2@1$1@1$0#i0@2$h2^a^8@2$7@1$1@1$0#i0^5>0@3$3$4@1$h3^6$c>0@3$3@1$2@2$8$6$5@1$h6^7@2$7@2$8$6$5@4$e$6$5@4$h7^6^5^4^3+4@3$3@1$h4$9@2$h5^d@5$b?2fx^c^b^a^9@2$h1$9@5$b?2fxM4\0$4@2$a@1$0#5@1$1@1$0#k0@3$h9@1$0#5^6@3$hf@1$0#5ZKv$f@2$i0@1$0#5Z^c@3$hd^c^6@3$hb^7@2$hc^c^5@3$ha@1$0#c@1$0#k0^4@2$he^b+4^a^9").
Proof.
ltac2:(KReplay.run1z (kr_t_PropExec ()) ["WithFP2"] "##nep'0h01bi001bh11oh27Hdecodeh36Hecallh46Hfetchh53immh63memh72oph82pch92rdh:4regsh;3romh<2rsh=4s!s8#>1wi01!s'#21ci036c_fcsri047c_f!s[#i054c_pci066c_!s8%7!s0$svi081ii093iszi0:2m'i0;1pi0<1ri0=6reporti0>3st'i0?1xp%0p&0p;1p;2p;3p;4p;5p;8p;6g00BRk101Tg001:j1;!s/$_j1^!s/#2Dj1G!s/$bj1L!s/#00j2~!s/#o1R0j1STg03Qmj2_Tg011\j2J!sC#9>j32!sA#Roj1e!s/#SoR1j2c!s1#TOj1V!s/#U@j4p!sU#5Lj1o!s8$lj4K!s/#VLR2j1n!s1#WTj1m!s/#X[j56!s/#Y`j3\!s/#Zlj1Q!s/#[jj3k!s/#\oj3j!s/#^5j3i!t&#B2j1t!s8#_:j1g!s/#`Bj1f!s/#aJj2Y!u-#3Aj3X!sS#8Qj3P!sA#bTj2d!sA#99j3A!s/#Vgj34!sA#cYj39!s8#S6j2O!s8#d`j1M!s/#e_j18!s/#f_j1N!s/#g`k200!s0#h^j1U!s/#i]j15!s/#j\j1T!s/#kZj8!sJ#1;Qj2b!s8#laj5!wY#3mJj3a!s/#n1j3`!s/#o<j2RTg040@j1}!s/$ij1|!s/#1Sj1{!u=#E_j1z!s8#2:j1x!s/$cj1w!s/#3Lj2]!s/#4Sj1l!sS#3Ej1C!s8#!wL#v!s/#6Tj1u!v6$dj3B!s8#7[j2E!s/#8Ej5<!s\$mj2[!s8#95j1s!y0$\j6>!s8#:<j1h!s/#;Jj1r!s/#<Gj2q!s/#=Cj2y!s/$fj3@!s/#>mj2DTf2R3g04@5R4f1R5f0R63@'Dp=F1D46p=Wf6R7f5R8f4R9f3R:?435P6D<p=:g04A<R;P:P3P5CK=@96,R8p==f7R<P!s>1]89@47!t##?!t##9235p=3P;P7P8P9!sQ%D1P6CKp=7A@356,R:p=H!s1%]:9@49,D8p=IP<!sZ/P6G0,D4p=Zg0162$01g004GR=#;R>#^#GR?%;>R>#;R@#;#;RA#;#GRB#LRC'~RD%G@#L#S\CRE%GA#LRA!uL#e%L?S00Q00%^=!s]##!sx#L%SARFf9RG/_<1JA932!t;#lRH%e8g00=ORI!s9#4BQRJg006gRK'cRL#SRM%V7PJPK!u/'Cp%o>R>CK,JL32PF1JA<%n4RNP0PA%m4RO#nRPP6f>RQp,2fxRRf=RSf<RTf;RUf:RVD6;\6RW!sW#PPPRPTPUPVPGD6RX#QRY=kSUP!sD&AjSY!s3#2P4PPAiSYUg04C=#tRW9FO6S01%gORZ%fOR[n10110?00031010>0000!s:,2!s:#1!s8I,Y4PRPHPD!v9#oR\g017PS025X?R]9P?7PT1dT8AA=B9R^54<99T7R_n!sb#!s##2!s'#1OU>R`!uO%#WRa32X1FPHPIP2POPNPHPPP6%MX%8X%NX%^@#oQ!t1$-00X,JC%UX%5XPY%TXG0=FO!v0#LPPf8RY#VP1!wZ$PP6P21c;ER@#mS03PPf@RI1bB6S04PRf?RFPQPSPTD6Rb#M%8b%Nb%5b%UbD17a5%Qb3`P1P;PEPP1R@6S05%}5S06%|5S07%{5S08%zCRb%x5S09%w5S0:P6PRfBfAS0;PIPFD6#TG01]@3Rc5FOn20!vo'1201!vt#:PZP!wf3=!wf$!sR%;!sR'8109Rd!v:#%lY!s[$!vr0Re!ws/!s_%!sH011R4!w4#f%g4Rg%f4Rh!sX%<!tE0=2NaX0HPM!vd$!}K&CpS0<P!{@%!wj&!w8$P6PdP!tG6PfPgP!t,=1MPH%C8S0=!ss&!w,&P@P@PEPHP;%C7RMPTPT%vRRaPUPbPb%uRRe!yK#G0Rd#8S0>1bB>Ri9BBURj%5dRdPbD1S0?P?PCP7P<PHPCQ0=1bB\Rk1ET8Rl!vS1P^PTF:Q0>PjP!sc$!sE2VPWE=POP;PDP5P9n!uF#!vj$501061041051!uT#7S0@!sL&:!sL@AP;PCP5P3!sL@BPbP;%S!sO#6!sO@CP;PAP5P5!sL@DP6PUG0S0E!w$/YS0!{i#QPaPS!v~#PePT!sM#Rm#8RnABBSiRo%5mRm!v8#Rp!vt$YPG!vt#%C<S0GPk1EQ<S0H!vU1!~[#7RqPQF:PnPoP!sf$!vx2TPWG?!{u0!u6#!{u#!yQ<RrPHP!uA#TP!#3V1PaP`!u8&!y5$53N!{%#H%C9S0I!s\$!yc#HPCP6PkP!xs2=4<^99T7!szA93NrX0HQ!sv$H!zv;Q0GPSPSPaPT!sc&UPVG0Rr#8R_ABBTiRs%5rRr!zh%J!vr$!zf$!th#1ES7Rt!vk58Ru54YRvPSD<P_PsP!se$!t~2U!zj%Q0@Q0AQ!yY#Q0CQ!xj$TG0Rw!xi/GPFPFPaPQ!ts&S!sI$x#8RyABBQiRz%5xRx!ts%K!ts$GPV!tu$3!tu#FYS0L!tv5<S0MPFF:PyPzP!sd$!tr2S!xdU!x+#!vt$A9S<v!wj31OT>Rv!w1/53NP6PM!wk?P6P!{3&A4GkqR{PQD<S0N!zk,S0O!zn5!v|;SG0R|!t+-3PIPIPaPF!te&Q!sH$}#8R~ABBFiS0P%5}R}!t7%Q!tX$VPUPk!va#YS0RPIF:S0SP~Q0PP!sM$!t[2Q!veYP6PQA9QY{S0T!vg5S>R{!~e/!vg%CPv!ve8QPnP6!vK#PTF7PWCHPOP!u{'IP~P3!u/#PQ!sB#EI!tyRQPaP!tY3X0C!|e$!xZ/ZS0U,[NPs%sTS0VE>!tx7Q0J!|%'P!{j&Q0K!zHWQ0U52NeS0U!v4;Q!yZ$!v5:Q!x@#!v6_Q0T!v79A4YkuS0T99S<!vA5S!vA$Q!v>;!#40$!t&#!#3c,PU!u4+!#3>&!~b'kQ!~B1PS!uBYS!vj#!#:T#001020101b0!}h<MQ!#=l&A4<k^!|+#TD<!#=OCQ!#;8-Q0FPpQ!~87!|[XMPTQ0S!#9/D53Ne!#4>JQ0H=4GqRq!#4@$H!#4@-S!#4@8!}++!#4%#Q!#3V+1EIGQ!#3S$Ro!#3R{qRq!uu4!#3M4Q!|B?!u\#!#3Q:o!#3Qaq!|@<tuR{!|?7Rv!|>GP{!|=IQ0L!|>h=2Nv!|<Zl^Rl!|;\!z36!|;[A9T7!#HM2!|96!u[3AP?9]%h9!wT:!ty$=PUPUPaPV!ss&GPYG0R`#8RlABBViRp%5`R`!uq#!v5$8P7!#J9$IPk1EU9!#@X4:R=PUF:PlPp!tq#!vQ4G!#>M<VG0!#D>/Q!#Cl'Y!#Aw#MPkP!#Cj1PuPSF:!#C`>!#AlX=PU1dU9=47=99U8R=!#>44V>R>!vT/!wI#AP?8]R]%h8!w;+2Q03PPQ0<PR!#W8$PYD6Re#M%8e%Ne%5e%UeD15ai%QeRi5`T!wn'Q05Q06Q07Q08!vD#9Q!#S'$!#T'$PUD6Ra#T!#Tu#c!#R}N!ur>!#WF#P]PUP!ug3>!u/%#WR]52Ne%V<R7P6!u\+!#R2$7!#V@-!un&4%Ma%8a%Na%5a%Ua!#Uy%a5`F!u_CQ!#U`$PQ!#Ub$!u^S!#U]6!#U[$<!#U[4!#T8Q]e%e<P5E>A\Te<,Y4!s:#R<eP<e1_TVP3E>!#\Z$%reR3,_TA\SX6RX!#\o%kTi3P!s3'j!s3%!#\|%Ti3Q01!uJ6!#\i`!u&$1qTe!xR%Q021y?\d9X?\9P?8!x`=!{=#W2W3W4W5W<W9W7W>X;EW6X8CW:W=o"). Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma step_sltiu : ltac2:(zQ "i11!h9!jc!in5!vd!o7!hga!mlb!is5!mm4!mmb!m7!mrb!hk6!ime!ms3!q2!ir3!msa!mt7!mu5!mv1!ng3!nj1!ki4!njf!q6!nl1!nl9!nm3!nmd!tb!u0!hpb&>0@1$1@1$0#k0@1$2@1$1@1$0#8>4segs@1$d$h0>4regs@2$a@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>2rd@1$1@1$0#5>2rs@1$1@1$0#5>3imm@1$1@1$0#c>0@3$3@1$2@1$1@1$0#i0@2$h2^9^7@2$7@1$1@1$0#i0^4>0@3$3$4@1$h3^5$c>0@3$3@1$2@2$8$6$5@1$h6^6@2$7@2$8$6$5@4$e$6$5@4$h8$h7^5^4^3+4@3$3@1$h4$9@2$h5^c@5$b?2fx^b^a^9^8@2$h1$9@5$b?2fxM4\0$4@2$a@1$0#5@1$1@1$0#k0@3$h9@1$0#5^6@3$he@1$0#5ZKv$f@2$hf@1$0#5Z^b@3$hb^b^6@2$hd@2$ha^b^5@2$i0@1$0#c^4@2$hc^a+4^9^8").
Proof.
ltac2:(KReplay.run1z (kr_t_PropExec ()) ["WithFP2"] "##1Ph01bh13immh21mh33memh42pch52rdh64regsh73romh82rsh94s!s8#:1wp;1p;2p;3p;4p;5p;6p;=g00BRj1PTg001:j10!s/$_j1;!s/#2Dj12!s/$bj14!s/#00j2K!s/#o1j17Tg03Qmj2ETg011\j2:!sA#9>j33!sA#Roj1C!s/#Soj2A!s/#TOj1@!s/#U@j4O!sS#5Lj1N!s8$lj4M!s/#VLj1J!sw#3Aj3H!sJ#8Qj38!sA#bTj2<!sA#99j3G!s/#Vgj3F!sA#cYj35!s8#S6j2>!s8#X[j51Tg04>mj26!sA#:ij29!s/#koj2=!t$#3mj2D!sJ#DBj3I!uW$\j6?!s8#<Gj2B!s/#ELl=L!s\#62#Pg004GR0#0R1#;#2R2%01R1#0R3#!s;#4#0#2R5#4R6'KR7%23#4#7\6R3%24#4R4%42R8%;0!sT##2R0#4%74f8R9f6R:'Ef3R;,:433!t6#lR4f4R<#Cg00=O!s:#4BQR!wy#6gR>'AR?#7f5R@#@P=P>g01m7R>P<P;f2R=CO%N1R1CM,:?!sa$@5R?#JRAp,2fxRBP4P7!s~#og017P5H2RC982@RDf:RE1<E<RFAG05;5F>R595E@n01!xm#002!s'#f9RG/>1RHP9f7RID1,6?f0RJP!t#$A82:CRCf;R21<2@190<'=952:!sk11>E1R1PGP9!sf$RK53AX2AP6190;,=FRL!su%PCP2A52:J!se1P!sa,=3AKX06!sU&DPEA5E@L!sU2HP9P!tx%,DAP5AIF0;E?PBPE!sn#!sA$B2P2!s5'P:P>P@!vn#P=f1PJM=LE?UUUW1X88W5W:X73W3X46W6W9o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma step_ecall : ltac2:(zQ "h91!h9!jc!in5!vd!is5!mmb!ire!o7!ime!nn8!q2!ir3!nnf!msa!mt7!mu5!mv1!ng3!m7!np7!nq1!nl1!mrb!tb!u0&>0@1$1@1$0#k0@1$2@1$1@1$0#8>4segs@1$8$b>4regs@2$h2@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>0@3$3@1$2@1$1@1$0#i0@2$e^6^4@2$4@1$1@1$0#i0^1>0@3$3$7@1$f^2$9@3$3@1$h0$5@2$h1^8@5$h6?2fx^7^6^5^4@2$d$5@8$c^7@1$h4?2fx^6@2$4@1$1@1$0#k0@2$h5^7@3$h7@1$0#5+h1Kv$a@2$h8@1$0#5+h1@1$6@1$1@1$0#k0@1$h3?2fx^5^4").
Proof.
ltac2:(KReplay.run1z (kr_t_PropExec ()) ["WithFP2"] "##;2p'0h06Hecallh16Hfetchh21bh33memh41oh52pch64regsh73romh84s!s3#91wi00!s'#11ci021ii033iszi042m'i051pi061ri076reporti083st'i091xp;1p;2p;3p;5p;8p;6g00BRj1iTg001:j14!s/$_j1J!s/#2Dj16!s/$bj1D!s/#00j2[!s/#o1R0j1MTg03Qmj2=Tg011\j22!sC#9>j31!sA#Roj1G!s/#VLR1j1F!s1#WTj1E!s/#X[j55!s/#Y`j3?!s/#Zlj1>!s/#[jj3P!s/#\oj3N!s/#^5j3R!t&#B2j1WTg04=fj37!s/#>mj20!sJ#_:j1L!s/#`Bj1K!s/#aJj29!sJ#5Lj1V!se#!s/#U!t{#3Aj3H!sJ#bTj2:!sA#E_j1T!sS#6Tj1S!sA#kZj83!s/#d`j18!s/#e_j1C!s/#f_j1A!s/#g`j2O!s/#h^j1<!s/#i]j1;!s/#j\j1B!s/#SoR2j2I!s1#TOj1h!tN#;Qj2g!s8#laj5f!s/#mJj3c!s/#n1j3b!s/#o<j2@!t`#0@j1`!s/$ij1_!s/#1Sj1\!s/#2:j1Z!s/$cj1]!s/#3Lj2^!s/#4Sj1Y!uP#3mj2a!x,$\j6Q!sA#;Jj1X!s/#<Gj2d!vm$Cj2e!tg#62#ig004G#4R3#J#6R4%43!s3$4#4R5#4#6R6#DR7'[%63#D#M\7R8%65#DR5%M5R9f5R:f3R;'=f0R<,2531!sx#lR=f1R>#Gg00:6R?31P9f2R@,25g04@5RA#FRBP0P5%EARC#FRDP<f9REp,2fxRFf8RGf7RHf6RIP:D5;?<RJ!sU#PDPFPHPIP:f4RKD5RL#>RM=PGIP!sF&ANGM!s3#1PAPDARGMIg04C=#WRJ97A<,0CRN%LCRO%KCRPn101109000310108!{^#!s:,2!s:#!s8J,9APH%VFRQPI%J3#UR3g017PRR5H4RS,:H,27%T7RT%SFRUP:PKG3,0ARV31X49P=P?P1PCPBP=PDP<%8L%CL%AL1OLS!s`#<L%;LPM%BLG3=7AJ,0CP0g04BQRMg006gR?'IPD%h;P2PMP?!sk#P1g04A<R?/I8RM#EPDf;R91g6<PFf:R6PEPGPHD5RE#8%CE%AE%;E%<EDf7c>%>E3bP2P?P8PD1@M<%`>%_>%\>PT%Z>%]>P!sm#=f<P9P6D5#BG31^M@57A,0Cn20!v@'120!vL$4POP!w737!vk$!sR%5!sR'2103!u|#%Y;!sY$!w#%002!w@3!s[%!sF011@!xS#A%LA%KA!sS%6!t<0=1BVX2=PIPQP:1:I!v|#PTPUPKP;!wX%=,aBPF!y{#!s:#D5RF!v=#F%AF1OF!wS%F%;F%>FRS%BF!wV&@A,0A=1B=e%G@P<EQA?HF@,9!s:$R@eP@e1=H:P>EQ!zh%%XFR>,=HA?GL<RL!z}&PHS>P!s3'N!s3%!{2&!s3#N!vc6!zta!u%$1dH!ug#QP:PR1e43d9H43,:I!v:351BeW0W1W9X78W3X57W6W8o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma bv_signed_small : ltac2:(zQ "80!h9!hq7!vd!hga!hl4!hif!jc!hpb>1x@1$6@1$0#k0>0@2$4@2$1@1$0#k0^1@2$5+2+jf@3$2$3@2$7@1$0#k0^2@2$1@1$0#k0^2").
Proof.
ltac2:(KReplay.run1z (kr_t_PropExec ()) ["WithFP2"] "##2lh02Hah14__p1h26__sat1h3!s/%3h44__x1h51Hh62Hxh77__arithh84__ffh9!sP%0h:!s/%2h;8__varmaph<5__with=1xp;1p;2p;3p;4p;6p;7p;8g001:j12Tg002Dj1B!s/$bj1M!s/#7Ej26!s/#5Lj18!s/#1_j13!s8$jj2<!s/#;2j20Tg01XVj1J!s8$Nj27!s/#@Ej2>!s/$mj3=!s/#AQj2Y!s/#3mj2A!s/#B2j1V!s/$Rj1U!s/#C2j2T!s/$Pj1Q!s/$nj1O!s/#DYj29!s/#E<j2N!s/#Jcj45!s/#N]j6L!sA$_j1I!sA$@j3HTg03JXj2G!s8#Fej2K!s/#GGj2F!s/#9>j3@!s/#H3j3E!s/$Rj4D!s\#K;j1P!s8#:Vj2?!s8$Xj3C!u`#:ij2R!tC$9j7S!s/#OAj7X!s/$ej8W!s/#=oR0f0R1'?p=1f1R2g00Q0R3!s,#OR4P4!s/#oR5P1g00ROFSp=4f2R6P3P4P4P5P2P1FXp=:f3R7!s;+6!s=#GWp=;g004GR8#2R9#2!s$'R:#BR;#M16;1%89R9%38#3!s$%R<#8R='<R>'016;2R?%J2%1?%8:R:,<9R@,0?'71>9=1009RA%1!s/#>[RB[%19RC!tv#oRDA=9=2UW0%1>\D^0C1>9:%1:100@[R=\AA=9:2VDX0C%1@!sH$P!ur#SK1Y09'APAeRAO1P=f4P!s-#Bp-0RBg006gRAg00T1R=#V%U=1TA2%QA%OAR=PA19A0g00PIRC1NA8R8C5,4=P=!v8+7EL5:=%I4R4P=PAP!{@#T]19A9%B<5HAR<!sX$R9P4PA1GA<PCP!sk%=:=9C;C;1K=5P1P6!vx#lR=!xh#6R5'A1F16=@=5dAEA02CDb8b;b<W4W1%11/72102>%P>/?6106>'7[[^4A^1BP1f9,6;R1/0@P1f7f8O4b7b3b2b9b2b:b3b55C;1R;2=@A?eW6W=o"). Qed.

Lemma bv_signed_hi : ltac2:(zQ "90!h9!hif!hq7!vd!hga!hk0!hr5!jc!hpb>1x@1$7@1$0#k0>0@2$5@2$1+2+jf@2$2@1$0#k0^1@3$3$4@2$8@1$0#k0^2@2$6@2$2@1$0#k0^2@2$1+2+k0").
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP2"] "p'0h01xh11Hh22Hah36__sat1h44__x1h52H0h62Hxh77__arithh84__ffh96__sat0h:8__varmaph;5__with<1eh=1zi001np;1p;2p;3p;6p;4p;7p;8p;5g001:j11Tg002Dj1:Tg002bj1BTg005Lj16Tg001_j12Tg005jj29Tg007Ej23Tg00:Vj20Tg01Bkj1@Tg00hUj27Tg009>j34Tg003mj28Tg00k@j2;Tg00jdj6WTg03LEj2VTg03E=j1UTg00@Ej2OTg00;2j25Tg00@mj3NTg00AQj2LTg00B2j1KTg00BRj1HTg00C2j2ATg00CPj1CTg00Cnj1DTg00DYj2ETg00J@j3FTg00E<j2GTg00Jcj4?Tg00N9j7ITg00E_j1JTg00Oej8>Tg00Fej2=Tg00GGj2MTg00H3j3<Tg00HRj4PTg01XVj1QTg03Ldj5RTg000\j6STg01:ij2TTg004GR0#1R1#1#1#1#1#1R2#:R3#BR4%61R1%20#2#2#2#2R5#6R6'9R7f0R8,33R9'0g006gR:f1R;,33R<%@3'7f2R=,33%62,91R2'794:8X=:17<2R>,8:1;3<P3P<g009XR?g01@=R@743RAP?P3P?p-0P8g02^<RBg00RoRCn0110000020010000X<?g017PP@P8EWPB1VB8b5W1%UAe1O16g00=oRA/51RB10A615A7[R@[10A1R?AN16;VCW210A7\C^2?P;g00SK1LA1'8PBeO1P@g00T1R@#K%H@1A:;%C:%D:R@g00Q0RBg00QOR?P?g00QoRCP@PBP?P?PCP:1E:1%:55F:g00PI1G:0C?g00ROFIR0%J?P0G>1=@CP8P=g004lRCg00:6R@'81M8==4C@dA<:A;CPb8b:b;X4:1078107;[^4:P8f5,33f4O2b7b3b9b3g00;N10A91592R915<2%Q8P8n2001000000120000000X04P9^04P8P=O1b1DRES1T3;=4:>eW6W0o"). Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
End WithFP2.

Section WithFP3.
Context {fx : FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma bv_wrap8_mod : ltac2:(zQ "60!hga!vd!h9!hi5!hif!hj6>1z$0@3$1$0@2$5@1$2#8^1@2$3^1@2$4+2+8").
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP3"] "h01zp;1p;2g001:j10Tg005Lj11Tg005jj23Tg006Gj22Tg003mj24Tg006gR0f0g004G#0R1#1%01#0#1'3'2,40W0o"). Qed.

Lemma bytes_le_Z_to_le : ltac2:(zQ "a0!hga!jh2!vd!nqc!jnf!hk0!hi5!hrc!jp9!hif>1k$1>1z$0>0@2$5Z^1@3$2$0@1$4@2$3^3^2@2$6^2@2$9+2@2$7+8@1$8^3").
Proof.
ltac2:(KReplay.run1z (kr_t_PropExec ()) ["WithFP3"] "##Pbh04__x1h17__arithh24__ffh38__varmaph45__with5!sQ#2h61bh71zh81xh91Hh:1kh;1nh<3Hi8h=3Hikh>2Hzh?1ah@1ohA2HihB2IHhC4cstrhD1ihE1mhF1yp&0p;2p;1p;3p;6p;4p;<p;8p;Bp;7g04F[j2NTg01@[j1JTg001:j1Y!s/#5Lj1Z!s/#9>j3Fj1x!s2#3mj2>!s/#6Gj2BTg04GXj1k!s8#0\j6D!s/#cgj25!sz#E=R0j1A!s:#b9R1j21!s1#2Dk10=!sF#;Qj2e!s9#7Ej2d!s8#AXj2L!s8#UDj2G!s/#^5R2j1H!s1#fdk20!si$5jj2S!s/#gJj20!t9$]j1v!s/#K`j4u!s/#ILl<p!s/#H;j1g!sS#B2j1l!s/$Rj1j!s/#C2j2]!s/$Pj1i!s/$nj1h!s/#DYj2Q!s/#E<j2\!s/#aVj3[!s/#i2j3P!s/#Jcj4O!s/#Fek20!v+#0GGk20!uh$H3k30@!s0$Rk40?!tY#F;k40!v]$;ij23j1w!s2#Vcj2C!s/#hUj2!sX#3J3j2c!sM$2j26!s/#:Vj29!s/#?FR3j2b!w@#H9k10<!tr$_k10;!t0#JXj3a!sC$Xk30:!v`$Tj2V!s/#[ak20!vL#0e0j3~!s/#_=j3U!s/$fj2`!s/#`Rj3_!s/#IDj1}!tm$Ej4y!sy#I?j4M!uw$Uj8z!s8$jj4{!w&$`j2|!u#$NR4j2T!sC#JOj4W!s/#K;k102!wc$;j4s!sM#W@k303!sC$Zk304!s:#jdk60!yN#4L=k10!um#1=kk207!s:#MJk208!s:#5Qk40!v&#1LCl<^!s/$hlBo!sj#N9j7f!s/#Oej8n!s/$Aj7m!s/#=oR5f0R6'9p=4f1R7%A6'1p==f2R81S76'Bp=:!{@#gR9?F76p=8g0171R:P:P9P9P2P0P0f3R2g01N2P8P7P6M<^p=t!sG&9!sG$5R0f4R;P!sH/r!sF&!s$%1P6P7P8P1P2P;P0f6R1f7R<f8R=f9R>MBop=qP7g00Q0R?!s,#OR@P@!s/#oRAP6g00RORBFfp=E1S87,B2/36p=!sX#4lRC!u4%;1B87!s>$XP9!st$T]P6COp=KP2P?P@P@PA!tr%Gnp=2PC!vD#ORD!u0'EDp=IP8!sQ+!sk%PI!sk#P!tL$<PCP!u_+!sU#?!sU-7P6Fmp=R%46R?1N87#J!tn#GRB#YRE#ZRF%YE#YRG#ZRH/=85:7'8[^79RIX:!vo#5AF956X791>95%ZBRJ,B7%k7ED!{%#YRK/N7#J1=HK9:7F'8eX>?X79P9157HRL%A2RM,1HRN7:F&0=GRG1eG8'd1L6H'G%H;,=HRO9:8FRP'8!s`$201G7RQ158H%A;RR!se#S7:F/LH,G6/8PX79RPP91SFHRT,B7PP10NHRN%H2RP#ARU!sX#V'8RW10MJRX!s5#Y,8N!xf#%x9RZP6X89R[PZ1876#vXF9X89PNPN1>9NPVPYP[!s$$9P9g01MN1176Cu,>9XE9X;9PHPH1>9HPUPX!sN#%A6!sB#8:PPPX106JRX!sv#2PM1>9MCtErM:qM<p%g2%4M!xr#1RM#lR[%jMRU1]97RY%i9RN%h!tk#91Q9HR\1\9BRB5[9R]=P9\R^g00kgR_1Q9J9P9B9[9\CO'E20BZA!zP#P8g00:6RJ,>C20A68=FCJdB0@957H0?RJb2b3b4X0911H6/0HR`11HX'8^09P6%A0RXO1b1bCH0>PWP910SH1B2T152H!sO#RX!wK%'GRSA:2F6!wv$%g;%4R10XH9:2F1B0TRX/37150H1=H<7:FRR/LHRW/37Ra'CP1PF1=H=/0HP8C7Rb,;6X6C1@7HRc,3RAX1T8/C6/;b!s=#c7H167HRb19H7Rd'bP3168H19H8AX<T215<H!sw$>Re1@2HRfC7'CP<PF10eHP2C7';P6162H13=;Re15>HPFf;Rg#ARh!y0#i1@0HC7Rj,C6P>!s^#iHRiP0C7Rk';X6CRlPe13>0Rm/Cj/!t|%Cm6/;mX6C&0<e15=Hf:Re!{1#m!ug#j1@;HRn'3RoP[PUPYPNPZ1KB\,EZRp&0;@R@Aa9B\Rq1Q95Rr'K,EZC2PAP!wk-66HRs16c5[!wg$P0P7O2R5b1:0:jnCIP=!t{#mHRmP;C7P=PmP;%HKRn#H,V9Rj2009H1V9n5~91V9KRK5U95U9g00f8Rn'`=_M!tl#91]98P7%}9CyRt!ty#PpP@PZ1\9ERE9<ZrP@A[9\ERu!zG#,KB!u=#vC2!u#2X59%48Rw11H2/0H,68[\s^09^5!u4#h!u6#P1O4b1CMD?AX=T;RTP=PHP;!vC,!tH$p!t#2Pb!sn$P5!sa%W<P6O119H2PlPo1;6k!y?$;m16;m19m;!y;%0i19i015e!x^#<Ri!wd#01@1HC7Pe!vX#0HR0P1!y7'1015gH!y[#<HR3'3RmPiPFf>#ARk,1H!zm#=C7!zk%Rl103HRs,3gPl13g<1@=!sH#,3i!y6%P9PC%wgRiPiPsP<PC\9/>i!u]+9AP9q\P_PBCO,EZ!xe1@6!sq#/86!xd%=!}J#GzPgPFf=!u:#_!}p#iP<C7RsPgPiP<!s~$!x#%vP@Pv!w^511H7!wY$6Rb11H8Rp!sk#h,67!yr#!wg%kP=P7O3Rx!w+%PmPgPHP3!wb,A<Z\BRmP@A<Zrq!zl39H6Ry%4c!zk&=P;O2b1C{D?!w4#P_P3C7RzPe!s0#!u#11Kqu!{e5!u+#6cp\b!to&!te&W=!xk%01PlAFCD!}D$>CDP!v&&AU9Kj/`n,|K!{E#RM!t8'A<Z^ERK!{?#!u6#BRB!u?%^=RZK!{2719`7R`%47R^%4h19h2'T[!vM,=PkP7P>O4R>b1CWCIP!uS'!tA+P!t<$P!t7&]Aa9E\9<Z]5RZ!|K9p19pf'T\^\`!t6&!t&&!ul%n20010!s#$21!s/#!s'$b@1CDo&02oD?P!|_5!wv&\=RZm!tB2%4H/Td\y!|j'!t7#!|j$!t7;PaPRPHP7!t,-BP@PB!s~2RJP^\?^09!#:4$P7!xx$sD?1GXW/37B03XW7D?XA?XD9604Sb9POP6J05b9PQ&067ED1eG7,dG207G!s4#N2L#JP8PLP41576#4Pw[1587#4\^R^1528#4\w20876P6!u6-12!s-%0X;9X?9P^^;9^?!x/#8PHPJP!tp#2P8!tp#O3b9O2!t:#P7#JA:7FV!#@^'XB!#AF#6H09X::o"). Qed.

Lemma bytes_le_N : ltac2:(zQ "c0!h9!jh2!vd!hga!jnf!nrd!hi5!hrc!jp9!hif!jc!hq7>1k$1>1v@1$a@1$0#k0@3$2$3@1$4@2$5^2^1@2$6@2$b@1$0#k0^1@2$9+2@2$7+8@1$8^2").
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP3"] "h01xh11Hh21kh31vp;1p;2p;3g001:j10Tg002Dj1?Tg002bj1;Tg007Ej23Tg00:Vj24Tg005Lj11Tg005jj22Tg00;2j2:Tg01XVj17Tg04N1j36Tg04OBj25Tg01@[j18Tg01E=j19Tg00b9j2>Tg006Gj2=Tg009>j3<Tg0171g004G#0R0#0#0R1#0#0#0R2#?R3#;R4f1R5f0R6,33R7g00;Ng00=oR8/47R9%10R0%12'2,:71335,48%76P5n2001000000120000000X04P9^04P6P5O1b136g006g1556#8%11%95'>,20,=73<eW3W2o"). Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

End WithFP3.
(* [comment removed for export] *)
