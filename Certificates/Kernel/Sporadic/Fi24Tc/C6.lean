module

public import Certificates.Kernel.Sporadic.Fi24Tc.Data
public import CFSG.Certificates.Kernel.Ssa3Split
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

#kc_repo #kc_ktree CFSG.KD.Fi24Tc KV6 "Certificates/Kernel/Sporadic/Fi24Tc/data/v6.bin" 152491 4 17841447 206496131367943209

public section

open CFSG.KD.Fi24Tc CFSG.KC.Ssa3 CFSG.KC.Ssa3Split

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v804 : Nat := CFSG.KD.Fi24Tc.KV6 0
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v805 : Nat := CFSG.KD.Fi24Tc.KV6 1
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l806 : List Nat := [CFSG.KD.Fi24Tc.Pc.v804, CFSG.KD.Fi24Tc.Pc.v805]
theorem CFSG.KD.Fi24Tc.Pc.p804 : Nat.beq (runC AR SD 804 (ckL CFSG.KD.Fi24Tc.Pc.l806) 2 804 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v806 : Nat := CFSG.KD.Fi24Tc.KV6 2
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v807 : Nat := CFSG.KD.Fi24Tc.KV6 3
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l808 : List Nat := [CFSG.KD.Fi24Tc.Pc.v804, CFSG.KD.Fi24Tc.Pc.v805, CFSG.KD.Fi24Tc.Pc.v806, CFSG.KD.Fi24Tc.Pc.v807]
theorem CFSG.KD.Fi24Tc.Pc.p806 : Nat.beq (runC AR SD 804 (ckL CFSG.KD.Fi24Tc.Pc.l808) 2 806 CFSG.KD.Fi24Tc.Pc.l806) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v808 : Nat := CFSG.KD.Fi24Tc.KV6 4
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v809 : Nat := CFSG.KD.Fi24Tc.KV6 5
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l810 : List Nat := [CFSG.KD.Fi24Tc.Pc.v804, CFSG.KD.Fi24Tc.Pc.v805, CFSG.KD.Fi24Tc.Pc.v806, CFSG.KD.Fi24Tc.Pc.v807, CFSG.KD.Fi24Tc.Pc.v808, CFSG.KD.Fi24Tc.Pc.v809]
theorem CFSG.KD.Fi24Tc.Pc.p808 : Nat.beq (runC AR SD 804 (ckL CFSG.KD.Fi24Tc.Pc.l810) 2 808 CFSG.KD.Fi24Tc.Pc.l808) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f120 : Nat.beq (runC AR SD 804 (finC AR SD (nat_lit 120) 804 812) 2 810 CFSG.KD.Fi24Tc.Pc.l810) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk120 : chk (nat_lit 120) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 120) (lo := 804) (hi := 812) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 806) CFSG.KD.Fi24Tc.Pc.p804 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 808) CFSG.KD.Fi24Tc.Pc.p806 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 810) CFSG.KD.Fi24Tc.Pc.p808 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f120

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a812_3 : Nat := CFSG.KD.Fi24Tc.KV6 6
theorem CFSG.KD.Fi24Tc.Pc.q812_3 : Nat.beq (powTop AR.mul (getV AR SD 812 [] (SD.na.getD 812 0)) (SD.nk.getD 812 1) 3 (ckP CFSG.KD.Fi24Tc.Pc.a812_3) 13 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a812_2 : Nat := CFSG.KD.Fi24Tc.KV6 7
theorem CFSG.KD.Fi24Tc.Pc.q812_2 : Nat.beq (powTop AR.mul (getV AR SD 812 [] (SD.na.getD 812 0)) (SD.nk.getD 812 1) 2 (ckP CFSG.KD.Fi24Tc.Pc.a812_2) 1 CFSG.KD.Fi24Tc.Pc.a812_3 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a812_1 : Nat := CFSG.KD.Fi24Tc.KV6 8
theorem CFSG.KD.Fi24Tc.Pc.q812_1 : Nat.beq (powTop AR.mul (getV AR SD 812 [] (SD.na.getD 812 0)) (SD.nk.getD 812 1) 1 (ckP CFSG.KD.Fi24Tc.Pc.a812_1) 1 CFSG.KD.Fi24Tc.Pc.a812_2 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v812 : Nat := CFSG.KD.Fi24Tc.KV6 9
theorem CFSG.KD.Fi24Tc.Pc.r812 : Nat.beq (powR AR.mul AR.one (getV AR SD 812 [] (SD.na.getD 812 0)) (SD.nk.getD 812 1) 1 CFSG.KD.Fi24Tc.Pc.a812_1 true) CFSG.KD.Fi24Tc.Pc.v812 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l813 : List Nat := [CFSG.KD.Fi24Tc.Pc.v812]
theorem CFSG.KD.Fi24Tc.Pc.f121 : Nat.beq (runC AR SD 812 (finC AR SD (nat_lit 121) 812 815) 2 813 CFSG.KD.Fi24Tc.Pc.l813) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk121 : chk (nat_lit 121) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 121) (lo := 812) (hi := 815) (m := 3) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) (runC_node (m := 3) (m2 := 2) (j2 := 813) (Lr := CFSG.KD.Fi24Tc.Pc.l813) ((nodeV_pow (R := AR) (D := SD) (lo := 812) (L := []) (j := 812) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 812 [] (SD.na.getD 812 0)) (SD.nk.getD 812 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Tc.Pc.q812_3 rfl).trans ((powR_seq (n := 3) CFSG.KD.Fi24Tc.Pc.q812_2 rfl).trans ((powR_seq (n := 2) CFSG.KD.Fi24Tc.Pc.q812_1 rfl).trans (powR_last CFSG.KD.Fi24Tc.Pc.r812)))))) (by quickRfl) rfl rfl rfl))).trans CFSG.KD.Fi24Tc.Pc.f121

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v815 : Nat := CFSG.KD.Fi24Tc.KV6 10
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v816 : Nat := CFSG.KD.Fi24Tc.KV6 11
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l817 : List Nat := [CFSG.KD.Fi24Tc.Pc.v815, CFSG.KD.Fi24Tc.Pc.v816]
theorem CFSG.KD.Fi24Tc.Pc.p815 : Nat.beq (runC AR SD 815 (ckL CFSG.KD.Fi24Tc.Pc.l817) 2 815 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v817 : Nat := CFSG.KD.Fi24Tc.KV6 12
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v818 : Nat := CFSG.KD.Fi24Tc.KV6 13
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l819 : List Nat := [CFSG.KD.Fi24Tc.Pc.v815, CFSG.KD.Fi24Tc.Pc.v816, CFSG.KD.Fi24Tc.Pc.v817, CFSG.KD.Fi24Tc.Pc.v818]
theorem CFSG.KD.Fi24Tc.Pc.p817 : Nat.beq (runC AR SD 815 (ckL CFSG.KD.Fi24Tc.Pc.l819) 2 817 CFSG.KD.Fi24Tc.Pc.l817) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v819 : Nat := CFSG.KD.Fi24Tc.KV6 14
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v820 : Nat := CFSG.KD.Fi24Tc.KV6 15
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l821 : List Nat := [CFSG.KD.Fi24Tc.Pc.v815, CFSG.KD.Fi24Tc.Pc.v816, CFSG.KD.Fi24Tc.Pc.v817, CFSG.KD.Fi24Tc.Pc.v818, CFSG.KD.Fi24Tc.Pc.v819, CFSG.KD.Fi24Tc.Pc.v820]
theorem CFSG.KD.Fi24Tc.Pc.p819 : Nat.beq (runC AR SD 815 (ckL CFSG.KD.Fi24Tc.Pc.l821) 2 819 CFSG.KD.Fi24Tc.Pc.l819) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f122 : Nat.beq (runC AR SD 815 (finC AR SD (nat_lit 122) 815 823) 2 821 CFSG.KD.Fi24Tc.Pc.l821) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk122 : chk (nat_lit 122) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 122) (lo := 815) (hi := 823) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 817) CFSG.KD.Fi24Tc.Pc.p815 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 819) CFSG.KD.Fi24Tc.Pc.p817 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 821) CFSG.KD.Fi24Tc.Pc.p819 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f122

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v823 : Nat := CFSG.KD.Fi24Tc.KV6 16
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v824 : Nat := CFSG.KD.Fi24Tc.KV6 17
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l825 : List Nat := [CFSG.KD.Fi24Tc.Pc.v823, CFSG.KD.Fi24Tc.Pc.v824]
theorem CFSG.KD.Fi24Tc.Pc.p823 : Nat.beq (runC AR SD 823 (ckL CFSG.KD.Fi24Tc.Pc.l825) 2 823 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v825 : Nat := CFSG.KD.Fi24Tc.KV6 18
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v826 : Nat := CFSG.KD.Fi24Tc.KV6 19
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l827 : List Nat := [CFSG.KD.Fi24Tc.Pc.v823, CFSG.KD.Fi24Tc.Pc.v824, CFSG.KD.Fi24Tc.Pc.v825, CFSG.KD.Fi24Tc.Pc.v826]
theorem CFSG.KD.Fi24Tc.Pc.p825 : Nat.beq (runC AR SD 823 (ckL CFSG.KD.Fi24Tc.Pc.l827) 2 825 CFSG.KD.Fi24Tc.Pc.l825) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v827 : Nat := CFSG.KD.Fi24Tc.KV6 20
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v828 : Nat := CFSG.KD.Fi24Tc.KV6 21
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l829 : List Nat := [CFSG.KD.Fi24Tc.Pc.v823, CFSG.KD.Fi24Tc.Pc.v824, CFSG.KD.Fi24Tc.Pc.v825, CFSG.KD.Fi24Tc.Pc.v826, CFSG.KD.Fi24Tc.Pc.v827, CFSG.KD.Fi24Tc.Pc.v828]
theorem CFSG.KD.Fi24Tc.Pc.p827 : Nat.beq (runC AR SD 823 (ckL CFSG.KD.Fi24Tc.Pc.l829) 2 827 CFSG.KD.Fi24Tc.Pc.l827) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f123 : Nat.beq (runC AR SD 823 (finC AR SD (nat_lit 123) 823 831) 2 829 CFSG.KD.Fi24Tc.Pc.l829) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk123 : chk (nat_lit 123) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 123) (lo := 823) (hi := 831) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 825) CFSG.KD.Fi24Tc.Pc.p823 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 827) CFSG.KD.Fi24Tc.Pc.p825 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 829) CFSG.KD.Fi24Tc.Pc.p827 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f123

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v831 : Nat := CFSG.KD.Fi24Tc.KV6 22
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v832 : Nat := CFSG.KD.Fi24Tc.KV6 23
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l833 : List Nat := [CFSG.KD.Fi24Tc.Pc.v831, CFSG.KD.Fi24Tc.Pc.v832]
theorem CFSG.KD.Fi24Tc.Pc.p831 : Nat.beq (runC AR SD 831 (ckL CFSG.KD.Fi24Tc.Pc.l833) 2 831 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v833 : Nat := CFSG.KD.Fi24Tc.KV6 24
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v834 : Nat := CFSG.KD.Fi24Tc.KV6 25
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l835 : List Nat := [CFSG.KD.Fi24Tc.Pc.v831, CFSG.KD.Fi24Tc.Pc.v832, CFSG.KD.Fi24Tc.Pc.v833, CFSG.KD.Fi24Tc.Pc.v834]
theorem CFSG.KD.Fi24Tc.Pc.p833 : Nat.beq (runC AR SD 831 (ckL CFSG.KD.Fi24Tc.Pc.l835) 2 833 CFSG.KD.Fi24Tc.Pc.l833) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v835 : Nat := CFSG.KD.Fi24Tc.KV6 26
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v836 : Nat := CFSG.KD.Fi24Tc.KV6 27
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l837 : List Nat := [CFSG.KD.Fi24Tc.Pc.v831, CFSG.KD.Fi24Tc.Pc.v832, CFSG.KD.Fi24Tc.Pc.v833, CFSG.KD.Fi24Tc.Pc.v834, CFSG.KD.Fi24Tc.Pc.v835, CFSG.KD.Fi24Tc.Pc.v836]
theorem CFSG.KD.Fi24Tc.Pc.p835 : Nat.beq (runC AR SD 831 (ckL CFSG.KD.Fi24Tc.Pc.l837) 2 835 CFSG.KD.Fi24Tc.Pc.l835) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f124 : Nat.beq (runC AR SD 831 (finC AR SD (nat_lit 124) 831 839) 2 837 CFSG.KD.Fi24Tc.Pc.l837) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk124 : chk (nat_lit 124) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 124) (lo := 831) (hi := 839) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 833) CFSG.KD.Fi24Tc.Pc.p831 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 835) CFSG.KD.Fi24Tc.Pc.p833 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 837) CFSG.KD.Fi24Tc.Pc.p835 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f124

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v839 : Nat := CFSG.KD.Fi24Tc.KV6 28
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v840 : Nat := CFSG.KD.Fi24Tc.KV6 29
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l841 : List Nat := [CFSG.KD.Fi24Tc.Pc.v839, CFSG.KD.Fi24Tc.Pc.v840]
theorem CFSG.KD.Fi24Tc.Pc.p839 : Nat.beq (runC AR SD 839 (ckL CFSG.KD.Fi24Tc.Pc.l841) 2 839 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v841 : Nat := CFSG.KD.Fi24Tc.KV6 30
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v842 : Nat := CFSG.KD.Fi24Tc.KV6 31
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l843 : List Nat := [CFSG.KD.Fi24Tc.Pc.v839, CFSG.KD.Fi24Tc.Pc.v840, CFSG.KD.Fi24Tc.Pc.v841, CFSG.KD.Fi24Tc.Pc.v842]
theorem CFSG.KD.Fi24Tc.Pc.p841 : Nat.beq (runC AR SD 839 (ckL CFSG.KD.Fi24Tc.Pc.l843) 2 841 CFSG.KD.Fi24Tc.Pc.l841) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v843 : Nat := CFSG.KD.Fi24Tc.KV6 32
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v844 : Nat := CFSG.KD.Fi24Tc.KV6 33
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l845 : List Nat := [CFSG.KD.Fi24Tc.Pc.v839, CFSG.KD.Fi24Tc.Pc.v840, CFSG.KD.Fi24Tc.Pc.v841, CFSG.KD.Fi24Tc.Pc.v842, CFSG.KD.Fi24Tc.Pc.v843, CFSG.KD.Fi24Tc.Pc.v844]
theorem CFSG.KD.Fi24Tc.Pc.p843 : Nat.beq (runC AR SD 839 (ckL CFSG.KD.Fi24Tc.Pc.l845) 2 843 CFSG.KD.Fi24Tc.Pc.l843) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f125 : Nat.beq (runC AR SD 839 (finC AR SD (nat_lit 125) 839 847) 2 845 CFSG.KD.Fi24Tc.Pc.l845) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk125 : chk (nat_lit 125) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 125) (lo := 839) (hi := 847) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 841) CFSG.KD.Fi24Tc.Pc.p839 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 843) CFSG.KD.Fi24Tc.Pc.p841 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 845) CFSG.KD.Fi24Tc.Pc.p843 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f125

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v847 : Nat := CFSG.KD.Fi24Tc.KV6 34
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v848 : Nat := CFSG.KD.Fi24Tc.KV6 35
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l849 : List Nat := [CFSG.KD.Fi24Tc.Pc.v847, CFSG.KD.Fi24Tc.Pc.v848]
theorem CFSG.KD.Fi24Tc.Pc.p847 : Nat.beq (runC AR SD 847 (ckL CFSG.KD.Fi24Tc.Pc.l849) 2 847 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a849_2 : Nat := CFSG.KD.Fi24Tc.KV6 36
theorem CFSG.KD.Fi24Tc.Pc.q849_2 : Nat.beq (powTop AR.mul (getV AR SD 847 CFSG.KD.Fi24Tc.Pc.l849 (SD.na.getD 849 0)) (SD.nk.getD 849 1) 2 (ckP CFSG.KD.Fi24Tc.Pc.a849_2) 14 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a849_1 : Nat := CFSG.KD.Fi24Tc.KV6 37
theorem CFSG.KD.Fi24Tc.Pc.q849_1 : Nat.beq (powTop AR.mul (getV AR SD 847 CFSG.KD.Fi24Tc.Pc.l849 (SD.na.getD 849 0)) (SD.nk.getD 849 1) 1 (ckP CFSG.KD.Fi24Tc.Pc.a849_1) 1 CFSG.KD.Fi24Tc.Pc.a849_2 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v849 : Nat := CFSG.KD.Fi24Tc.KV6 38
theorem CFSG.KD.Fi24Tc.Pc.r849 : Nat.beq (powR AR.mul AR.one (getV AR SD 847 CFSG.KD.Fi24Tc.Pc.l849 (SD.na.getD 849 0)) (SD.nk.getD 849 1) 1 CFSG.KD.Fi24Tc.Pc.a849_1 true) CFSG.KD.Fi24Tc.Pc.v849 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l850 : List Nat := [CFSG.KD.Fi24Tc.Pc.v847, CFSG.KD.Fi24Tc.Pc.v848, CFSG.KD.Fi24Tc.Pc.v849]
theorem CFSG.KD.Fi24Tc.Pc.f126 : Nat.beq (runC AR SD 847 (finC AR SD (nat_lit 126) 847 851) 1 850 CFSG.KD.Fi24Tc.Pc.l850) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk126 : chk (nat_lit 126) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 126) (lo := 847) (hi := 851) (m := 4) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 4) (m2 := 2) (j2 := 849) CFSG.KD.Fi24Tc.Pc.p847 rfl rfl).trans (runC_node (m := 2) (m2 := 1) (j2 := 850) (Lr := CFSG.KD.Fi24Tc.Pc.l850) ((nodeV_pow (R := AR) (D := SD) (lo := 847) (L := CFSG.KD.Fi24Tc.Pc.l849) (j := 849) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 847 CFSG.KD.Fi24Tc.Pc.l849 (SD.na.getD 849 0)) (SD.nk.getD 849 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Tc.Pc.q849_2 rfl).trans ((powR_seq (n := 2) CFSG.KD.Fi24Tc.Pc.q849_1 rfl).trans (powR_last CFSG.KD.Fi24Tc.Pc.r849))))) (by quickRfl) rfl rfl rfl)))).trans CFSG.KD.Fi24Tc.Pc.f126

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v851 : Nat := CFSG.KD.Fi24Tc.KV6 39
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v852 : Nat := CFSG.KD.Fi24Tc.KV6 40
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l853 : List Nat := [CFSG.KD.Fi24Tc.Pc.v851, CFSG.KD.Fi24Tc.Pc.v852]
theorem CFSG.KD.Fi24Tc.Pc.p851 : Nat.beq (runC AR SD 851 (ckL CFSG.KD.Fi24Tc.Pc.l853) 2 851 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v853 : Nat := CFSG.KD.Fi24Tc.KV6 41
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v854 : Nat := CFSG.KD.Fi24Tc.KV6 42
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l855 : List Nat := [CFSG.KD.Fi24Tc.Pc.v851, CFSG.KD.Fi24Tc.Pc.v852, CFSG.KD.Fi24Tc.Pc.v853, CFSG.KD.Fi24Tc.Pc.v854]
theorem CFSG.KD.Fi24Tc.Pc.p853 : Nat.beq (runC AR SD 851 (ckL CFSG.KD.Fi24Tc.Pc.l855) 2 853 CFSG.KD.Fi24Tc.Pc.l853) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v855 : Nat := CFSG.KD.Fi24Tc.KV6 43
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v856 : Nat := CFSG.KD.Fi24Tc.KV6 44
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l857 : List Nat := [CFSG.KD.Fi24Tc.Pc.v851, CFSG.KD.Fi24Tc.Pc.v852, CFSG.KD.Fi24Tc.Pc.v853, CFSG.KD.Fi24Tc.Pc.v854, CFSG.KD.Fi24Tc.Pc.v855, CFSG.KD.Fi24Tc.Pc.v856]
theorem CFSG.KD.Fi24Tc.Pc.p855 : Nat.beq (runC AR SD 851 (ckL CFSG.KD.Fi24Tc.Pc.l857) 2 855 CFSG.KD.Fi24Tc.Pc.l855) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f127 : Nat.beq (runC AR SD 851 (finC AR SD (nat_lit 127) 851 859) 2 857 CFSG.KD.Fi24Tc.Pc.l857) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk127 : chk (nat_lit 127) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 127) (lo := 851) (hi := 859) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 853) CFSG.KD.Fi24Tc.Pc.p851 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 855) CFSG.KD.Fi24Tc.Pc.p853 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 857) CFSG.KD.Fi24Tc.Pc.p855 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f127

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v859 : Nat := CFSG.KD.Fi24Tc.KV6 45
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v860 : Nat := CFSG.KD.Fi24Tc.KV6 46
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l861 : List Nat := [CFSG.KD.Fi24Tc.Pc.v859, CFSG.KD.Fi24Tc.Pc.v860]
theorem CFSG.KD.Fi24Tc.Pc.p859 : Nat.beq (runC AR SD 859 (ckL CFSG.KD.Fi24Tc.Pc.l861) 2 859 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v861 : Nat := CFSG.KD.Fi24Tc.KV6 47
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v862 : Nat := CFSG.KD.Fi24Tc.KV6 48
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l863 : List Nat := [CFSG.KD.Fi24Tc.Pc.v859, CFSG.KD.Fi24Tc.Pc.v860, CFSG.KD.Fi24Tc.Pc.v861, CFSG.KD.Fi24Tc.Pc.v862]
theorem CFSG.KD.Fi24Tc.Pc.p861 : Nat.beq (runC AR SD 859 (ckL CFSG.KD.Fi24Tc.Pc.l863) 2 861 CFSG.KD.Fi24Tc.Pc.l861) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v863 : Nat := CFSG.KD.Fi24Tc.KV6 49
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v864 : Nat := CFSG.KD.Fi24Tc.KV6 50
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l865 : List Nat := [CFSG.KD.Fi24Tc.Pc.v859, CFSG.KD.Fi24Tc.Pc.v860, CFSG.KD.Fi24Tc.Pc.v861, CFSG.KD.Fi24Tc.Pc.v862, CFSG.KD.Fi24Tc.Pc.v863, CFSG.KD.Fi24Tc.Pc.v864]
theorem CFSG.KD.Fi24Tc.Pc.p863 : Nat.beq (runC AR SD 859 (ckL CFSG.KD.Fi24Tc.Pc.l865) 2 863 CFSG.KD.Fi24Tc.Pc.l863) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f128 : Nat.beq (runC AR SD 859 (finC AR SD (nat_lit 128) 859 867) 2 865 CFSG.KD.Fi24Tc.Pc.l865) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk128 : chk (nat_lit 128) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 128) (lo := 859) (hi := 867) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 861) CFSG.KD.Fi24Tc.Pc.p859 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 863) CFSG.KD.Fi24Tc.Pc.p861 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 865) CFSG.KD.Fi24Tc.Pc.p863 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f128

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v867 : Nat := CFSG.KD.Fi24Tc.KV6 51
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v868 : Nat := CFSG.KD.Fi24Tc.KV6 52
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l869 : List Nat := [CFSG.KD.Fi24Tc.Pc.v867, CFSG.KD.Fi24Tc.Pc.v868]
theorem CFSG.KD.Fi24Tc.Pc.p867 : Nat.beq (runC AR SD 867 (ckL CFSG.KD.Fi24Tc.Pc.l869) 2 867 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v869 : Nat := CFSG.KD.Fi24Tc.KV6 53
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v870 : Nat := CFSG.KD.Fi24Tc.KV6 54
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l871 : List Nat := [CFSG.KD.Fi24Tc.Pc.v867, CFSG.KD.Fi24Tc.Pc.v868, CFSG.KD.Fi24Tc.Pc.v869, CFSG.KD.Fi24Tc.Pc.v870]
theorem CFSG.KD.Fi24Tc.Pc.p869 : Nat.beq (runC AR SD 867 (ckL CFSG.KD.Fi24Tc.Pc.l871) 2 869 CFSG.KD.Fi24Tc.Pc.l869) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v871 : Nat := CFSG.KD.Fi24Tc.KV6 55
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v872 : Nat := CFSG.KD.Fi24Tc.KV6 56
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l873 : List Nat := [CFSG.KD.Fi24Tc.Pc.v867, CFSG.KD.Fi24Tc.Pc.v868, CFSG.KD.Fi24Tc.Pc.v869, CFSG.KD.Fi24Tc.Pc.v870, CFSG.KD.Fi24Tc.Pc.v871, CFSG.KD.Fi24Tc.Pc.v872]
theorem CFSG.KD.Fi24Tc.Pc.p871 : Nat.beq (runC AR SD 867 (ckL CFSG.KD.Fi24Tc.Pc.l873) 2 871 CFSG.KD.Fi24Tc.Pc.l871) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f129 : Nat.beq (runC AR SD 867 (finC AR SD (nat_lit 129) 867 875) 2 873 CFSG.KD.Fi24Tc.Pc.l873) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk129 : chk (nat_lit 129) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 129) (lo := 867) (hi := 875) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 869) CFSG.KD.Fi24Tc.Pc.p867 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 871) CFSG.KD.Fi24Tc.Pc.p869 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 873) CFSG.KD.Fi24Tc.Pc.p871 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f129

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v875 : Nat := CFSG.KD.Fi24Tc.KV6 57
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v876 : Nat := CFSG.KD.Fi24Tc.KV6 58
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l877 : List Nat := [CFSG.KD.Fi24Tc.Pc.v875, CFSG.KD.Fi24Tc.Pc.v876]
theorem CFSG.KD.Fi24Tc.Pc.p875 : Nat.beq (runC AR SD 875 (ckL CFSG.KD.Fi24Tc.Pc.l877) 2 875 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a877_1 : Nat := CFSG.KD.Fi24Tc.KV6 59
theorem CFSG.KD.Fi24Tc.Pc.q877_1 : Nat.beq (powTop AR.mul (getV AR SD 875 CFSG.KD.Fi24Tc.Pc.l877 (SD.na.getD 877 0)) (SD.nk.getD 877 1) 1 (ckP CFSG.KD.Fi24Tc.Pc.a877_1) 15 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v877 : Nat := CFSG.KD.Fi24Tc.KV6 60
theorem CFSG.KD.Fi24Tc.Pc.r877 : Nat.beq (powR AR.mul AR.one (getV AR SD 875 CFSG.KD.Fi24Tc.Pc.l877 (SD.na.getD 877 0)) (SD.nk.getD 877 1) 1 CFSG.KD.Fi24Tc.Pc.a877_1 true) CFSG.KD.Fi24Tc.Pc.v877 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l878 : List Nat := [CFSG.KD.Fi24Tc.Pc.v875, CFSG.KD.Fi24Tc.Pc.v876, CFSG.KD.Fi24Tc.Pc.v877]
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v878 : Nat := CFSG.KD.Fi24Tc.KV6 61
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v879 : Nat := CFSG.KD.Fi24Tc.KV6 62
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l880 : List Nat := [CFSG.KD.Fi24Tc.Pc.v875, CFSG.KD.Fi24Tc.Pc.v876, CFSG.KD.Fi24Tc.Pc.v877, CFSG.KD.Fi24Tc.Pc.v878, CFSG.KD.Fi24Tc.Pc.v879]
theorem CFSG.KD.Fi24Tc.Pc.p878 : Nat.beq (runC AR SD 875 (ckL CFSG.KD.Fi24Tc.Pc.l880) 2 878 CFSG.KD.Fi24Tc.Pc.l878) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f130 : Nat.beq (runC AR SD 875 (finC AR SD (nat_lit 130) 875 881) 1 880 CFSG.KD.Fi24Tc.Pc.l880) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk130 : chk (nat_lit 130) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 130) (lo := 875) (hi := 881) (m := 6) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 6) (m2 := 4) (j2 := 877) CFSG.KD.Fi24Tc.Pc.p875 rfl rfl).trans ((runC_node (m := 4) (m2 := 3) (j2 := 878) (Lr := CFSG.KD.Fi24Tc.Pc.l878) ((nodeV_pow (R := AR) (D := SD) (lo := 875) (L := CFSG.KD.Fi24Tc.Pc.l877) (j := 877) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 875 CFSG.KD.Fi24Tc.Pc.l877 (SD.na.getD 877 0)) (SD.nk.getD 877 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Tc.Pc.q877_1 rfl).trans (powR_last CFSG.KD.Fi24Tc.Pc.r877)))) (by quickRfl) rfl rfl rfl).trans (runC_seq (m := 3) (m2 := 1) (j2 := 880) CFSG.KD.Fi24Tc.Pc.p878 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f130

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v881 : Nat := CFSG.KD.Fi24Tc.KV6 63
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v882 : Nat := CFSG.KD.Fi24Tc.KV6 64
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l883 : List Nat := [CFSG.KD.Fi24Tc.Pc.v881, CFSG.KD.Fi24Tc.Pc.v882]
theorem CFSG.KD.Fi24Tc.Pc.p881 : Nat.beq (runC AR SD 881 (ckL CFSG.KD.Fi24Tc.Pc.l883) 2 881 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v883 : Nat := CFSG.KD.Fi24Tc.KV6 65
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v884 : Nat := CFSG.KD.Fi24Tc.KV6 66
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l885 : List Nat := [CFSG.KD.Fi24Tc.Pc.v881, CFSG.KD.Fi24Tc.Pc.v882, CFSG.KD.Fi24Tc.Pc.v883, CFSG.KD.Fi24Tc.Pc.v884]
theorem CFSG.KD.Fi24Tc.Pc.p883 : Nat.beq (runC AR SD 881 (ckL CFSG.KD.Fi24Tc.Pc.l885) 2 883 CFSG.KD.Fi24Tc.Pc.l883) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v885 : Nat := CFSG.KD.Fi24Tc.KV6 67
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v886 : Nat := CFSG.KD.Fi24Tc.KV6 68
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l887 : List Nat := [CFSG.KD.Fi24Tc.Pc.v881, CFSG.KD.Fi24Tc.Pc.v882, CFSG.KD.Fi24Tc.Pc.v883, CFSG.KD.Fi24Tc.Pc.v884, CFSG.KD.Fi24Tc.Pc.v885, CFSG.KD.Fi24Tc.Pc.v886]
theorem CFSG.KD.Fi24Tc.Pc.p885 : Nat.beq (runC AR SD 881 (ckL CFSG.KD.Fi24Tc.Pc.l887) 2 885 CFSG.KD.Fi24Tc.Pc.l885) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f131 : Nat.beq (runC AR SD 881 (finC AR SD (nat_lit 131) 881 889) 2 887 CFSG.KD.Fi24Tc.Pc.l887) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk131 : chk (nat_lit 131) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 131) (lo := 881) (hi := 889) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 883) CFSG.KD.Fi24Tc.Pc.p881 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 885) CFSG.KD.Fi24Tc.Pc.p883 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 887) CFSG.KD.Fi24Tc.Pc.p885 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f131

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v889 : Nat := CFSG.KD.Fi24Tc.KV6 69
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v890 : Nat := CFSG.KD.Fi24Tc.KV6 70
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l891 : List Nat := [CFSG.KD.Fi24Tc.Pc.v889, CFSG.KD.Fi24Tc.Pc.v890]
theorem CFSG.KD.Fi24Tc.Pc.p889 : Nat.beq (runC AR SD 889 (ckL CFSG.KD.Fi24Tc.Pc.l891) 2 889 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v891 : Nat := CFSG.KD.Fi24Tc.KV6 71
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v892 : Nat := CFSG.KD.Fi24Tc.KV6 72
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l893 : List Nat := [CFSG.KD.Fi24Tc.Pc.v889, CFSG.KD.Fi24Tc.Pc.v890, CFSG.KD.Fi24Tc.Pc.v891, CFSG.KD.Fi24Tc.Pc.v892]
theorem CFSG.KD.Fi24Tc.Pc.p891 : Nat.beq (runC AR SD 889 (ckL CFSG.KD.Fi24Tc.Pc.l893) 2 891 CFSG.KD.Fi24Tc.Pc.l891) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v893 : Nat := CFSG.KD.Fi24Tc.KV6 73
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v894 : Nat := CFSG.KD.Fi24Tc.KV6 74
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l895 : List Nat := [CFSG.KD.Fi24Tc.Pc.v889, CFSG.KD.Fi24Tc.Pc.v890, CFSG.KD.Fi24Tc.Pc.v891, CFSG.KD.Fi24Tc.Pc.v892, CFSG.KD.Fi24Tc.Pc.v893, CFSG.KD.Fi24Tc.Pc.v894]
theorem CFSG.KD.Fi24Tc.Pc.p893 : Nat.beq (runC AR SD 889 (ckL CFSG.KD.Fi24Tc.Pc.l895) 2 893 CFSG.KD.Fi24Tc.Pc.l893) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f132 : Nat.beq (runC AR SD 889 (finC AR SD (nat_lit 132) 889 897) 2 895 CFSG.KD.Fi24Tc.Pc.l895) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk132 : chk (nat_lit 132) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 132) (lo := 889) (hi := 897) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 891) CFSG.KD.Fi24Tc.Pc.p889 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 893) CFSG.KD.Fi24Tc.Pc.p891 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 895) CFSG.KD.Fi24Tc.Pc.p893 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f132

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v897 : Nat := CFSG.KD.Fi24Tc.KV6 75
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v898 : Nat := CFSG.KD.Fi24Tc.KV6 76
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l899 : List Nat := [CFSG.KD.Fi24Tc.Pc.v897, CFSG.KD.Fi24Tc.Pc.v898]
theorem CFSG.KD.Fi24Tc.Pc.p897 : Nat.beq (runC AR SD 897 (ckL CFSG.KD.Fi24Tc.Pc.l899) 2 897 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v899 : Nat := CFSG.KD.Fi24Tc.KV6 77
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v900 : Nat := CFSG.KD.Fi24Tc.KV6 78
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l901 : List Nat := [CFSG.KD.Fi24Tc.Pc.v897, CFSG.KD.Fi24Tc.Pc.v898, CFSG.KD.Fi24Tc.Pc.v899, CFSG.KD.Fi24Tc.Pc.v900]
theorem CFSG.KD.Fi24Tc.Pc.p899 : Nat.beq (runC AR SD 897 (ckL CFSG.KD.Fi24Tc.Pc.l901) 2 899 CFSG.KD.Fi24Tc.Pc.l899) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v901 : Nat := CFSG.KD.Fi24Tc.KV6 79
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v902 : Nat := CFSG.KD.Fi24Tc.KV6 80
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l903 : List Nat := [CFSG.KD.Fi24Tc.Pc.v897, CFSG.KD.Fi24Tc.Pc.v898, CFSG.KD.Fi24Tc.Pc.v899, CFSG.KD.Fi24Tc.Pc.v900, CFSG.KD.Fi24Tc.Pc.v901, CFSG.KD.Fi24Tc.Pc.v902]
theorem CFSG.KD.Fi24Tc.Pc.p901 : Nat.beq (runC AR SD 897 (ckL CFSG.KD.Fi24Tc.Pc.l903) 2 901 CFSG.KD.Fi24Tc.Pc.l901) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f133 : Nat.beq (runC AR SD 897 (finC AR SD (nat_lit 133) 897 905) 2 903 CFSG.KD.Fi24Tc.Pc.l903) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk133 : chk (nat_lit 133) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 133) (lo := 897) (hi := 905) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 899) CFSG.KD.Fi24Tc.Pc.p897 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 901) CFSG.KD.Fi24Tc.Pc.p899 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 903) CFSG.KD.Fi24Tc.Pc.p901 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f133

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v905 : Nat := CFSG.KD.Fi24Tc.KV6 81
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v906 : Nat := CFSG.KD.Fi24Tc.KV6 82
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l907 : List Nat := [CFSG.KD.Fi24Tc.Pc.v905, CFSG.KD.Fi24Tc.Pc.v906]
theorem CFSG.KD.Fi24Tc.Pc.p905 : Nat.beq (runC AR SD 905 (ckL CFSG.KD.Fi24Tc.Pc.l907) 2 905 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v907 : Nat := CFSG.KD.Fi24Tc.KV6 83
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v908 : Nat := CFSG.KD.Fi24Tc.KV6 84
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l909 : List Nat := [CFSG.KD.Fi24Tc.Pc.v905, CFSG.KD.Fi24Tc.Pc.v906, CFSG.KD.Fi24Tc.Pc.v907, CFSG.KD.Fi24Tc.Pc.v908]
theorem CFSG.KD.Fi24Tc.Pc.p907 : Nat.beq (runC AR SD 905 (ckL CFSG.KD.Fi24Tc.Pc.l909) 2 907 CFSG.KD.Fi24Tc.Pc.l907) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v909 : Nat := CFSG.KD.Fi24Tc.KV6 85
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v910 : Nat := CFSG.KD.Fi24Tc.KV6 86
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l911 : List Nat := [CFSG.KD.Fi24Tc.Pc.v905, CFSG.KD.Fi24Tc.Pc.v906, CFSG.KD.Fi24Tc.Pc.v907, CFSG.KD.Fi24Tc.Pc.v908, CFSG.KD.Fi24Tc.Pc.v909, CFSG.KD.Fi24Tc.Pc.v910]
theorem CFSG.KD.Fi24Tc.Pc.p909 : Nat.beq (runC AR SD 905 (ckL CFSG.KD.Fi24Tc.Pc.l911) 2 909 CFSG.KD.Fi24Tc.Pc.l909) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f134 : Nat.beq (runC AR SD 905 (finC AR SD (nat_lit 134) 905 913) 2 911 CFSG.KD.Fi24Tc.Pc.l911) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk134 : chk (nat_lit 134) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 134) (lo := 905) (hi := 913) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 907) CFSG.KD.Fi24Tc.Pc.p905 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 909) CFSG.KD.Fi24Tc.Pc.p907 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 911) CFSG.KD.Fi24Tc.Pc.p909 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f134

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v913 : Nat := CFSG.KD.Fi24Tc.KV6 87
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v914 : Nat := CFSG.KD.Fi24Tc.KV6 88
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l915 : List Nat := [CFSG.KD.Fi24Tc.Pc.v913, CFSG.KD.Fi24Tc.Pc.v914]
theorem CFSG.KD.Fi24Tc.Pc.p913 : Nat.beq (runC AR SD 913 (ckL CFSG.KD.Fi24Tc.Pc.l915) 2 913 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v915 : Nat := CFSG.KD.Fi24Tc.KV6 89
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v916 : Nat := CFSG.KD.Fi24Tc.KV6 90
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l917 : List Nat := [CFSG.KD.Fi24Tc.Pc.v913, CFSG.KD.Fi24Tc.Pc.v914, CFSG.KD.Fi24Tc.Pc.v915, CFSG.KD.Fi24Tc.Pc.v916]
theorem CFSG.KD.Fi24Tc.Pc.p915 : Nat.beq (runC AR SD 913 (ckL CFSG.KD.Fi24Tc.Pc.l917) 2 915 CFSG.KD.Fi24Tc.Pc.l915) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v917 : Nat := CFSG.KD.Fi24Tc.KV6 91
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v918 : Nat := CFSG.KD.Fi24Tc.KV6 92
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l919 : List Nat := [CFSG.KD.Fi24Tc.Pc.v913, CFSG.KD.Fi24Tc.Pc.v914, CFSG.KD.Fi24Tc.Pc.v915, CFSG.KD.Fi24Tc.Pc.v916, CFSG.KD.Fi24Tc.Pc.v917, CFSG.KD.Fi24Tc.Pc.v918]
theorem CFSG.KD.Fi24Tc.Pc.p917 : Nat.beq (runC AR SD 913 (ckL CFSG.KD.Fi24Tc.Pc.l919) 2 917 CFSG.KD.Fi24Tc.Pc.l917) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f135 : Nat.beq (runC AR SD 913 (finC AR SD (nat_lit 135) 913 921) 2 919 CFSG.KD.Fi24Tc.Pc.l919) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk135 : chk (nat_lit 135) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 135) (lo := 913) (hi := 921) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 915) CFSG.KD.Fi24Tc.Pc.p913 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 917) CFSG.KD.Fi24Tc.Pc.p915 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 919) CFSG.KD.Fi24Tc.Pc.p917 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f135

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v921 : Nat := CFSG.KD.Fi24Tc.KV6 93
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v922 : Nat := CFSG.KD.Fi24Tc.KV6 94
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l923 : List Nat := [CFSG.KD.Fi24Tc.Pc.v921, CFSG.KD.Fi24Tc.Pc.v922]
theorem CFSG.KD.Fi24Tc.Pc.p921 : Nat.beq (runC AR SD 921 (ckL CFSG.KD.Fi24Tc.Pc.l923) 2 921 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v923 : Nat := CFSG.KD.Fi24Tc.KV6 95
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v924 : Nat := CFSG.KD.Fi24Tc.KV6 96
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l925 : List Nat := [CFSG.KD.Fi24Tc.Pc.v921, CFSG.KD.Fi24Tc.Pc.v922, CFSG.KD.Fi24Tc.Pc.v923, CFSG.KD.Fi24Tc.Pc.v924]
theorem CFSG.KD.Fi24Tc.Pc.p923 : Nat.beq (runC AR SD 921 (ckL CFSG.KD.Fi24Tc.Pc.l925) 2 923 CFSG.KD.Fi24Tc.Pc.l923) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v925 : Nat := CFSG.KD.Fi24Tc.KV6 97
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l926 : List Nat := [CFSG.KD.Fi24Tc.Pc.v921, CFSG.KD.Fi24Tc.Pc.v922, CFSG.KD.Fi24Tc.Pc.v923, CFSG.KD.Fi24Tc.Pc.v924, CFSG.KD.Fi24Tc.Pc.v925]
theorem CFSG.KD.Fi24Tc.Pc.p925 : Nat.beq (runC AR SD 921 (ckL CFSG.KD.Fi24Tc.Pc.l926) 1 925 CFSG.KD.Fi24Tc.Pc.l925) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v926 : Nat := CFSG.KD.Fi24Tc.KV6 98
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l927 : List Nat := [CFSG.KD.Fi24Tc.Pc.v921, CFSG.KD.Fi24Tc.Pc.v922, CFSG.KD.Fi24Tc.Pc.v923, CFSG.KD.Fi24Tc.Pc.v924, CFSG.KD.Fi24Tc.Pc.v925, CFSG.KD.Fi24Tc.Pc.v926]
theorem CFSG.KD.Fi24Tc.Pc.p926 : Nat.beq (runC AR SD 921 (ckL CFSG.KD.Fi24Tc.Pc.l927) 1 926 CFSG.KD.Fi24Tc.Pc.l926) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f136 : Nat.beq (runC AR SD 921 (finC AR SD (nat_lit 136) 921 928) 1 927 CFSG.KD.Fi24Tc.Pc.l927) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk136 : chk (nat_lit 136) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 136) (lo := 921) (hi := 928) (m := 7) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 7) (m2 := 5) (j2 := 923) CFSG.KD.Fi24Tc.Pc.p921 rfl rfl).trans ((runC_seq (m := 5) (m2 := 3) (j2 := 925) CFSG.KD.Fi24Tc.Pc.p923 rfl rfl).trans ((runC_seq (m := 3) (m2 := 2) (j2 := 926) CFSG.KD.Fi24Tc.Pc.p925 rfl rfl).trans (runC_seq (m := 2) (m2 := 1) (j2 := 927) CFSG.KD.Fi24Tc.Pc.p926 rfl rfl)))))).trans CFSG.KD.Fi24Tc.Pc.f136

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v928 : Nat := CFSG.KD.Fi24Tc.KV6 99
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v929 : Nat := CFSG.KD.Fi24Tc.KV6 100
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l930 : List Nat := [CFSG.KD.Fi24Tc.Pc.v928, CFSG.KD.Fi24Tc.Pc.v929]
theorem CFSG.KD.Fi24Tc.Pc.p928 : Nat.beq (runC AR SD 928 (ckL CFSG.KD.Fi24Tc.Pc.l930) 2 928 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v930 : Nat := CFSG.KD.Fi24Tc.KV6 101
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v931 : Nat := CFSG.KD.Fi24Tc.KV6 102
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l932 : List Nat := [CFSG.KD.Fi24Tc.Pc.v928, CFSG.KD.Fi24Tc.Pc.v929, CFSG.KD.Fi24Tc.Pc.v930, CFSG.KD.Fi24Tc.Pc.v931]
theorem CFSG.KD.Fi24Tc.Pc.p930 : Nat.beq (runC AR SD 928 (ckL CFSG.KD.Fi24Tc.Pc.l932) 2 930 CFSG.KD.Fi24Tc.Pc.l930) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v932 : Nat := CFSG.KD.Fi24Tc.KV6 103
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v933 : Nat := CFSG.KD.Fi24Tc.KV6 104
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l934 : List Nat := [CFSG.KD.Fi24Tc.Pc.v928, CFSG.KD.Fi24Tc.Pc.v929, CFSG.KD.Fi24Tc.Pc.v930, CFSG.KD.Fi24Tc.Pc.v931, CFSG.KD.Fi24Tc.Pc.v932, CFSG.KD.Fi24Tc.Pc.v933]
theorem CFSG.KD.Fi24Tc.Pc.p932 : Nat.beq (runC AR SD 928 (ckL CFSG.KD.Fi24Tc.Pc.l934) 2 932 CFSG.KD.Fi24Tc.Pc.l932) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f137 : Nat.beq (runC AR SD 928 (finC AR SD (nat_lit 137) 928 936) 2 934 CFSG.KD.Fi24Tc.Pc.l934) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk137 : chk (nat_lit 137) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 137) (lo := 928) (hi := 936) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 930) CFSG.KD.Fi24Tc.Pc.p928 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 932) CFSG.KD.Fi24Tc.Pc.p930 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 934) CFSG.KD.Fi24Tc.Pc.p932 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f137

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v936 : Nat := CFSG.KD.Fi24Tc.KV6 105
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v937 : Nat := CFSG.KD.Fi24Tc.KV6 106
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l938 : List Nat := [CFSG.KD.Fi24Tc.Pc.v936, CFSG.KD.Fi24Tc.Pc.v937]
theorem CFSG.KD.Fi24Tc.Pc.p936 : Nat.beq (runC AR SD 936 (ckL CFSG.KD.Fi24Tc.Pc.l938) 2 936 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v938 : Nat := CFSG.KD.Fi24Tc.KV6 107
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v939 : Nat := CFSG.KD.Fi24Tc.KV6 108
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l940 : List Nat := [CFSG.KD.Fi24Tc.Pc.v936, CFSG.KD.Fi24Tc.Pc.v937, CFSG.KD.Fi24Tc.Pc.v938, CFSG.KD.Fi24Tc.Pc.v939]
theorem CFSG.KD.Fi24Tc.Pc.p938 : Nat.beq (runC AR SD 936 (ckL CFSG.KD.Fi24Tc.Pc.l940) 2 938 CFSG.KD.Fi24Tc.Pc.l938) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v940 : Nat := CFSG.KD.Fi24Tc.KV6 109
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v941 : Nat := CFSG.KD.Fi24Tc.KV6 110
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l942 : List Nat := [CFSG.KD.Fi24Tc.Pc.v936, CFSG.KD.Fi24Tc.Pc.v937, CFSG.KD.Fi24Tc.Pc.v938, CFSG.KD.Fi24Tc.Pc.v939, CFSG.KD.Fi24Tc.Pc.v940, CFSG.KD.Fi24Tc.Pc.v941]
theorem CFSG.KD.Fi24Tc.Pc.p940 : Nat.beq (runC AR SD 936 (ckL CFSG.KD.Fi24Tc.Pc.l942) 2 940 CFSG.KD.Fi24Tc.Pc.l940) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f138 : Nat.beq (runC AR SD 936 (finC AR SD (nat_lit 138) 936 944) 2 942 CFSG.KD.Fi24Tc.Pc.l942) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk138 : chk (nat_lit 138) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 138) (lo := 936) (hi := 944) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 938) CFSG.KD.Fi24Tc.Pc.p936 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 940) CFSG.KD.Fi24Tc.Pc.p938 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 942) CFSG.KD.Fi24Tc.Pc.p940 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f138

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v944 : Nat := CFSG.KD.Fi24Tc.KV6 111
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v945 : Nat := CFSG.KD.Fi24Tc.KV6 112
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l946 : List Nat := [CFSG.KD.Fi24Tc.Pc.v944, CFSG.KD.Fi24Tc.Pc.v945]
theorem CFSG.KD.Fi24Tc.Pc.p944 : Nat.beq (runC AR SD 944 (ckL CFSG.KD.Fi24Tc.Pc.l946) 2 944 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v946 : Nat := CFSG.KD.Fi24Tc.KV6 113
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v947 : Nat := CFSG.KD.Fi24Tc.KV6 114
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l948 : List Nat := [CFSG.KD.Fi24Tc.Pc.v944, CFSG.KD.Fi24Tc.Pc.v945, CFSG.KD.Fi24Tc.Pc.v946, CFSG.KD.Fi24Tc.Pc.v947]
theorem CFSG.KD.Fi24Tc.Pc.p946 : Nat.beq (runC AR SD 944 (ckL CFSG.KD.Fi24Tc.Pc.l948) 2 946 CFSG.KD.Fi24Tc.Pc.l946) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v948 : Nat := CFSG.KD.Fi24Tc.KV6 115
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v949 : Nat := CFSG.KD.Fi24Tc.KV6 116
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l950 : List Nat := [CFSG.KD.Fi24Tc.Pc.v944, CFSG.KD.Fi24Tc.Pc.v945, CFSG.KD.Fi24Tc.Pc.v946, CFSG.KD.Fi24Tc.Pc.v947, CFSG.KD.Fi24Tc.Pc.v948, CFSG.KD.Fi24Tc.Pc.v949]
theorem CFSG.KD.Fi24Tc.Pc.p948 : Nat.beq (runC AR SD 944 (ckL CFSG.KD.Fi24Tc.Pc.l950) 2 948 CFSG.KD.Fi24Tc.Pc.l948) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f139 : Nat.beq (runC AR SD 944 (finC AR SD (nat_lit 139) 944 952) 2 950 CFSG.KD.Fi24Tc.Pc.l950) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk139 : chk (nat_lit 139) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 139) (lo := 944) (hi := 952) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 946) CFSG.KD.Fi24Tc.Pc.p944 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 948) CFSG.KD.Fi24Tc.Pc.p946 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 950) CFSG.KD.Fi24Tc.Pc.p948 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f139

end
