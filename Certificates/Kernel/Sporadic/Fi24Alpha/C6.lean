module

public import Certificates.Kernel.Sporadic.Fi24Alpha.Data
public import CFSG.Certificates.Kernel.Ssa3Split
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

#kc_repo #kc_ktree CFSG.KD.Fi24Alpha KV6 "Certificates/Kernel/Sporadic/Fi24Alpha/data/v6.bin" 152491 4 23788596 16442054573360087981

public section

open CFSG.KD.Fi24Alpha CFSG.KC.Ssa3 CFSG.KC.Ssa3Split

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v836 : Nat := CFSG.KD.Fi24Alpha.KV6 0
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v837 : Nat := CFSG.KD.Fi24Alpha.KV6 1
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l838 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v836, CFSG.KD.Fi24Alpha.Pc.v837]
theorem CFSG.KD.Fi24Alpha.Pc.p836 : Nat.beq (runC AR SD 836 (ckL CFSG.KD.Fi24Alpha.Pc.l838) 2 836 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v838 : Nat := CFSG.KD.Fi24Alpha.KV6 2
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v839 : Nat := CFSG.KD.Fi24Alpha.KV6 3
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l840 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v836, CFSG.KD.Fi24Alpha.Pc.v837, CFSG.KD.Fi24Alpha.Pc.v838, CFSG.KD.Fi24Alpha.Pc.v839]
theorem CFSG.KD.Fi24Alpha.Pc.p838 : Nat.beq (runC AR SD 836 (ckL CFSG.KD.Fi24Alpha.Pc.l840) 2 838 CFSG.KD.Fi24Alpha.Pc.l838) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v840 : Nat := CFSG.KD.Fi24Alpha.KV6 4
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v841 : Nat := CFSG.KD.Fi24Alpha.KV6 5
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l842 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v836, CFSG.KD.Fi24Alpha.Pc.v837, CFSG.KD.Fi24Alpha.Pc.v838, CFSG.KD.Fi24Alpha.Pc.v839, CFSG.KD.Fi24Alpha.Pc.v840, CFSG.KD.Fi24Alpha.Pc.v841]
theorem CFSG.KD.Fi24Alpha.Pc.p840 : Nat.beq (runC AR SD 836 (ckL CFSG.KD.Fi24Alpha.Pc.l842) 2 840 CFSG.KD.Fi24Alpha.Pc.l840) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v842 : Nat := CFSG.KD.Fi24Alpha.KV6 6
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v843 : Nat := CFSG.KD.Fi24Alpha.KV6 7
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l844 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v836, CFSG.KD.Fi24Alpha.Pc.v837, CFSG.KD.Fi24Alpha.Pc.v838, CFSG.KD.Fi24Alpha.Pc.v839, CFSG.KD.Fi24Alpha.Pc.v840, CFSG.KD.Fi24Alpha.Pc.v841, CFSG.KD.Fi24Alpha.Pc.v842, CFSG.KD.Fi24Alpha.Pc.v843]
theorem CFSG.KD.Fi24Alpha.Pc.p842 : Nat.beq (runC AR SD 836 (ckL CFSG.KD.Fi24Alpha.Pc.l844) 2 842 CFSG.KD.Fi24Alpha.Pc.l842) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v844 : Nat := CFSG.KD.Fi24Alpha.KV6 8
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v845 : Nat := CFSG.KD.Fi24Alpha.KV6 9
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l846 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v836, CFSG.KD.Fi24Alpha.Pc.v837, CFSG.KD.Fi24Alpha.Pc.v838, CFSG.KD.Fi24Alpha.Pc.v839, CFSG.KD.Fi24Alpha.Pc.v840, CFSG.KD.Fi24Alpha.Pc.v841, CFSG.KD.Fi24Alpha.Pc.v842, CFSG.KD.Fi24Alpha.Pc.v843, CFSG.KD.Fi24Alpha.Pc.v844, CFSG.KD.Fi24Alpha.Pc.v845]
theorem CFSG.KD.Fi24Alpha.Pc.p844 : Nat.beq (runC AR SD 836 (ckL CFSG.KD.Fi24Alpha.Pc.l846) 2 844 CFSG.KD.Fi24Alpha.Pc.l844) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v846 : Nat := CFSG.KD.Fi24Alpha.KV6 10
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v847 : Nat := CFSG.KD.Fi24Alpha.KV6 11
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l848 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v836, CFSG.KD.Fi24Alpha.Pc.v837, CFSG.KD.Fi24Alpha.Pc.v838, CFSG.KD.Fi24Alpha.Pc.v839, CFSG.KD.Fi24Alpha.Pc.v840, CFSG.KD.Fi24Alpha.Pc.v841, CFSG.KD.Fi24Alpha.Pc.v842, CFSG.KD.Fi24Alpha.Pc.v843, CFSG.KD.Fi24Alpha.Pc.v844, CFSG.KD.Fi24Alpha.Pc.v845, CFSG.KD.Fi24Alpha.Pc.v846, CFSG.KD.Fi24Alpha.Pc.v847]
theorem CFSG.KD.Fi24Alpha.Pc.p846 : Nat.beq (runC AR SD 836 (ckL CFSG.KD.Fi24Alpha.Pc.l848) 2 846 CFSG.KD.Fi24Alpha.Pc.l846) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v848 : Nat := CFSG.KD.Fi24Alpha.KV6 12
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v849 : Nat := CFSG.KD.Fi24Alpha.KV6 13
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l850 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v836, CFSG.KD.Fi24Alpha.Pc.v837, CFSG.KD.Fi24Alpha.Pc.v838, CFSG.KD.Fi24Alpha.Pc.v839, CFSG.KD.Fi24Alpha.Pc.v840, CFSG.KD.Fi24Alpha.Pc.v841, CFSG.KD.Fi24Alpha.Pc.v842, CFSG.KD.Fi24Alpha.Pc.v843, CFSG.KD.Fi24Alpha.Pc.v844, CFSG.KD.Fi24Alpha.Pc.v845, CFSG.KD.Fi24Alpha.Pc.v846, CFSG.KD.Fi24Alpha.Pc.v847, CFSG.KD.Fi24Alpha.Pc.v848, CFSG.KD.Fi24Alpha.Pc.v849]
theorem CFSG.KD.Fi24Alpha.Pc.p848 : Nat.beq (runC AR SD 836 (ckL CFSG.KD.Fi24Alpha.Pc.l850) 2 848 CFSG.KD.Fi24Alpha.Pc.l848) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v850 : Nat := CFSG.KD.Fi24Alpha.KV6 14
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v851 : Nat := CFSG.KD.Fi24Alpha.KV6 15
theorem CFSG.KD.Fi24Alpha.Pc.f60 : Nat.beq (runC AR SD 836 (finC AR SD (nat_lit 60) 836 852) 2 850 CFSG.KD.Fi24Alpha.Pc.l850) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk60 : chk (nat_lit 60) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 60) (lo := 836) (hi := 852) (m := 16) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 16) (m2 := 14) (j2 := 838) CFSG.KD.Fi24Alpha.Pc.p836 rfl rfl).trans ((runC_seq (m := 14) (m2 := 12) (j2 := 840) CFSG.KD.Fi24Alpha.Pc.p838 rfl rfl).trans ((runC_seq (m := 12) (m2 := 10) (j2 := 842) CFSG.KD.Fi24Alpha.Pc.p840 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 844) CFSG.KD.Fi24Alpha.Pc.p842 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 846) CFSG.KD.Fi24Alpha.Pc.p844 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 848) CFSG.KD.Fi24Alpha.Pc.p846 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 850) CFSG.KD.Fi24Alpha.Pc.p848 rfl rfl))))))))).trans CFSG.KD.Fi24Alpha.Pc.f60

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v852 : Nat := CFSG.KD.Fi24Alpha.KV6 16
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v853 : Nat := CFSG.KD.Fi24Alpha.KV6 17
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l854 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v852, CFSG.KD.Fi24Alpha.Pc.v853]
theorem CFSG.KD.Fi24Alpha.Pc.p852 : Nat.beq (runC AR SD 852 (ckL CFSG.KD.Fi24Alpha.Pc.l854) 2 852 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v854 : Nat := CFSG.KD.Fi24Alpha.KV6 18
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v855 : Nat := CFSG.KD.Fi24Alpha.KV6 19
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l856 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v852, CFSG.KD.Fi24Alpha.Pc.v853, CFSG.KD.Fi24Alpha.Pc.v854, CFSG.KD.Fi24Alpha.Pc.v855]
theorem CFSG.KD.Fi24Alpha.Pc.p854 : Nat.beq (runC AR SD 852 (ckL CFSG.KD.Fi24Alpha.Pc.l856) 2 854 CFSG.KD.Fi24Alpha.Pc.l854) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v856 : Nat := CFSG.KD.Fi24Alpha.KV6 20
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v857 : Nat := CFSG.KD.Fi24Alpha.KV6 21
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l858 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v852, CFSG.KD.Fi24Alpha.Pc.v853, CFSG.KD.Fi24Alpha.Pc.v854, CFSG.KD.Fi24Alpha.Pc.v855, CFSG.KD.Fi24Alpha.Pc.v856, CFSG.KD.Fi24Alpha.Pc.v857]
theorem CFSG.KD.Fi24Alpha.Pc.p856 : Nat.beq (runC AR SD 852 (ckL CFSG.KD.Fi24Alpha.Pc.l858) 2 856 CFSG.KD.Fi24Alpha.Pc.l856) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v858 : Nat := CFSG.KD.Fi24Alpha.KV6 22
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v859 : Nat := CFSG.KD.Fi24Alpha.KV6 23
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l860 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v852, CFSG.KD.Fi24Alpha.Pc.v853, CFSG.KD.Fi24Alpha.Pc.v854, CFSG.KD.Fi24Alpha.Pc.v855, CFSG.KD.Fi24Alpha.Pc.v856, CFSG.KD.Fi24Alpha.Pc.v857, CFSG.KD.Fi24Alpha.Pc.v858, CFSG.KD.Fi24Alpha.Pc.v859]
theorem CFSG.KD.Fi24Alpha.Pc.p858 : Nat.beq (runC AR SD 852 (ckL CFSG.KD.Fi24Alpha.Pc.l860) 2 858 CFSG.KD.Fi24Alpha.Pc.l858) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v860 : Nat := CFSG.KD.Fi24Alpha.KV6 24
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v861 : Nat := CFSG.KD.Fi24Alpha.KV6 25
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l862 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v852, CFSG.KD.Fi24Alpha.Pc.v853, CFSG.KD.Fi24Alpha.Pc.v854, CFSG.KD.Fi24Alpha.Pc.v855, CFSG.KD.Fi24Alpha.Pc.v856, CFSG.KD.Fi24Alpha.Pc.v857, CFSG.KD.Fi24Alpha.Pc.v858, CFSG.KD.Fi24Alpha.Pc.v859, CFSG.KD.Fi24Alpha.Pc.v860, CFSG.KD.Fi24Alpha.Pc.v861]
theorem CFSG.KD.Fi24Alpha.Pc.p860 : Nat.beq (runC AR SD 852 (ckL CFSG.KD.Fi24Alpha.Pc.l862) 2 860 CFSG.KD.Fi24Alpha.Pc.l860) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v862 : Nat := CFSG.KD.Fi24Alpha.KV6 26
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v863 : Nat := CFSG.KD.Fi24Alpha.KV6 27
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l864 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v852, CFSG.KD.Fi24Alpha.Pc.v853, CFSG.KD.Fi24Alpha.Pc.v854, CFSG.KD.Fi24Alpha.Pc.v855, CFSG.KD.Fi24Alpha.Pc.v856, CFSG.KD.Fi24Alpha.Pc.v857, CFSG.KD.Fi24Alpha.Pc.v858, CFSG.KD.Fi24Alpha.Pc.v859, CFSG.KD.Fi24Alpha.Pc.v860, CFSG.KD.Fi24Alpha.Pc.v861, CFSG.KD.Fi24Alpha.Pc.v862, CFSG.KD.Fi24Alpha.Pc.v863]
theorem CFSG.KD.Fi24Alpha.Pc.p862 : Nat.beq (runC AR SD 852 (ckL CFSG.KD.Fi24Alpha.Pc.l864) 2 862 CFSG.KD.Fi24Alpha.Pc.l862) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v864 : Nat := CFSG.KD.Fi24Alpha.KV6 28
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v865 : Nat := CFSG.KD.Fi24Alpha.KV6 29
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l866 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v852, CFSG.KD.Fi24Alpha.Pc.v853, CFSG.KD.Fi24Alpha.Pc.v854, CFSG.KD.Fi24Alpha.Pc.v855, CFSG.KD.Fi24Alpha.Pc.v856, CFSG.KD.Fi24Alpha.Pc.v857, CFSG.KD.Fi24Alpha.Pc.v858, CFSG.KD.Fi24Alpha.Pc.v859, CFSG.KD.Fi24Alpha.Pc.v860, CFSG.KD.Fi24Alpha.Pc.v861, CFSG.KD.Fi24Alpha.Pc.v862, CFSG.KD.Fi24Alpha.Pc.v863, CFSG.KD.Fi24Alpha.Pc.v864, CFSG.KD.Fi24Alpha.Pc.v865]
theorem CFSG.KD.Fi24Alpha.Pc.p864 : Nat.beq (runC AR SD 852 (ckL CFSG.KD.Fi24Alpha.Pc.l866) 2 864 CFSG.KD.Fi24Alpha.Pc.l864) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v866 : Nat := CFSG.KD.Fi24Alpha.KV6 30
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v867 : Nat := CFSG.KD.Fi24Alpha.KV6 31
theorem CFSG.KD.Fi24Alpha.Pc.f61 : Nat.beq (runC AR SD 852 (finC AR SD (nat_lit 61) 852 868) 2 866 CFSG.KD.Fi24Alpha.Pc.l866) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk61 : chk (nat_lit 61) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 61) (lo := 852) (hi := 868) (m := 16) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 16) (m2 := 14) (j2 := 854) CFSG.KD.Fi24Alpha.Pc.p852 rfl rfl).trans ((runC_seq (m := 14) (m2 := 12) (j2 := 856) CFSG.KD.Fi24Alpha.Pc.p854 rfl rfl).trans ((runC_seq (m := 12) (m2 := 10) (j2 := 858) CFSG.KD.Fi24Alpha.Pc.p856 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 860) CFSG.KD.Fi24Alpha.Pc.p858 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 862) CFSG.KD.Fi24Alpha.Pc.p860 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 864) CFSG.KD.Fi24Alpha.Pc.p862 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 866) CFSG.KD.Fi24Alpha.Pc.p864 rfl rfl))))))))).trans CFSG.KD.Fi24Alpha.Pc.f61

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v868 : Nat := CFSG.KD.Fi24Alpha.KV6 32
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v869 : Nat := CFSG.KD.Fi24Alpha.KV6 33
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l870 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v868, CFSG.KD.Fi24Alpha.Pc.v869]
theorem CFSG.KD.Fi24Alpha.Pc.p868 : Nat.beq (runC AR SD 868 (ckL CFSG.KD.Fi24Alpha.Pc.l870) 2 868 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v870 : Nat := CFSG.KD.Fi24Alpha.KV6 34
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v871 : Nat := CFSG.KD.Fi24Alpha.KV6 35
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l872 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v868, CFSG.KD.Fi24Alpha.Pc.v869, CFSG.KD.Fi24Alpha.Pc.v870, CFSG.KD.Fi24Alpha.Pc.v871]
theorem CFSG.KD.Fi24Alpha.Pc.p870 : Nat.beq (runC AR SD 868 (ckL CFSG.KD.Fi24Alpha.Pc.l872) 2 870 CFSG.KD.Fi24Alpha.Pc.l870) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v872 : Nat := CFSG.KD.Fi24Alpha.KV6 36
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v873 : Nat := CFSG.KD.Fi24Alpha.KV6 37
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l874 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v868, CFSG.KD.Fi24Alpha.Pc.v869, CFSG.KD.Fi24Alpha.Pc.v870, CFSG.KD.Fi24Alpha.Pc.v871, CFSG.KD.Fi24Alpha.Pc.v872, CFSG.KD.Fi24Alpha.Pc.v873]
theorem CFSG.KD.Fi24Alpha.Pc.p872 : Nat.beq (runC AR SD 868 (ckL CFSG.KD.Fi24Alpha.Pc.l874) 2 872 CFSG.KD.Fi24Alpha.Pc.l872) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v874 : Nat := CFSG.KD.Fi24Alpha.KV6 38
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v875 : Nat := CFSG.KD.Fi24Alpha.KV6 39
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l876 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v868, CFSG.KD.Fi24Alpha.Pc.v869, CFSG.KD.Fi24Alpha.Pc.v870, CFSG.KD.Fi24Alpha.Pc.v871, CFSG.KD.Fi24Alpha.Pc.v872, CFSG.KD.Fi24Alpha.Pc.v873, CFSG.KD.Fi24Alpha.Pc.v874, CFSG.KD.Fi24Alpha.Pc.v875]
theorem CFSG.KD.Fi24Alpha.Pc.p874 : Nat.beq (runC AR SD 868 (ckL CFSG.KD.Fi24Alpha.Pc.l876) 2 874 CFSG.KD.Fi24Alpha.Pc.l874) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.a876_1 : Nat := CFSG.KD.Fi24Alpha.KV6 40
theorem CFSG.KD.Fi24Alpha.Pc.q876_1 : Nat.beq (powTop AR.mul (getV AR SD 868 CFSG.KD.Fi24Alpha.Pc.l876 (SD.na.getD 876 0)) (SD.nk.getD 876 1) 1 (ckP CFSG.KD.Fi24Alpha.Pc.a876_1) 15 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v876 : Nat := CFSG.KD.Fi24Alpha.KV6 41
theorem CFSG.KD.Fi24Alpha.Pc.r876 : Nat.beq (powR AR.mul AR.one (getV AR SD 868 CFSG.KD.Fi24Alpha.Pc.l876 (SD.na.getD 876 0)) (SD.nk.getD 876 1) 1 CFSG.KD.Fi24Alpha.Pc.a876_1 true) CFSG.KD.Fi24Alpha.Pc.v876 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v877 : Nat := CFSG.KD.Fi24Alpha.KV6 42
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v878 : Nat := CFSG.KD.Fi24Alpha.KV6 43
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l877 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v868, CFSG.KD.Fi24Alpha.Pc.v869, CFSG.KD.Fi24Alpha.Pc.v870, CFSG.KD.Fi24Alpha.Pc.v871, CFSG.KD.Fi24Alpha.Pc.v872, CFSG.KD.Fi24Alpha.Pc.v873, CFSG.KD.Fi24Alpha.Pc.v874, CFSG.KD.Fi24Alpha.Pc.v875, CFSG.KD.Fi24Alpha.Pc.v876]
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l879 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v868, CFSG.KD.Fi24Alpha.Pc.v869, CFSG.KD.Fi24Alpha.Pc.v870, CFSG.KD.Fi24Alpha.Pc.v871, CFSG.KD.Fi24Alpha.Pc.v872, CFSG.KD.Fi24Alpha.Pc.v873, CFSG.KD.Fi24Alpha.Pc.v874, CFSG.KD.Fi24Alpha.Pc.v875, CFSG.KD.Fi24Alpha.Pc.v876, CFSG.KD.Fi24Alpha.Pc.v877, CFSG.KD.Fi24Alpha.Pc.v878]
theorem CFSG.KD.Fi24Alpha.Pc.p877 : Nat.beq (runC AR SD 868 (ckL CFSG.KD.Fi24Alpha.Pc.l879) 2 877 CFSG.KD.Fi24Alpha.Pc.l877) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v879 : Nat := CFSG.KD.Fi24Alpha.KV6 44
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v880 : Nat := CFSG.KD.Fi24Alpha.KV6 45
theorem CFSG.KD.Fi24Alpha.Pc.f62 : Nat.beq (runC AR SD 868 (finC AR SD (nat_lit 62) 868 881) 2 879 CFSG.KD.Fi24Alpha.Pc.l879) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk62 : chk (nat_lit 62) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 62) (lo := 868) (hi := 881) (m := 13) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 13) (m2 := 11) (j2 := 870) CFSG.KD.Fi24Alpha.Pc.p868 rfl rfl).trans ((runC_seq (m := 11) (m2 := 9) (j2 := 872) CFSG.KD.Fi24Alpha.Pc.p870 rfl rfl).trans ((runC_seq (m := 9) (m2 := 7) (j2 := 874) CFSG.KD.Fi24Alpha.Pc.p872 rfl rfl).trans ((runC_seq (m := 7) (m2 := 5) (j2 := 876) CFSG.KD.Fi24Alpha.Pc.p874 rfl rfl).trans ((runC_node (m := 5) (m2 := 4) (j2 := 877) (Lr := CFSG.KD.Fi24Alpha.Pc.l877) ((nodeV_pow (R := AR) (D := SD) (lo := 868) (L := CFSG.KD.Fi24Alpha.Pc.l876) (j := 876) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 868 CFSG.KD.Fi24Alpha.Pc.l876 (SD.na.getD 876 0)) (SD.nk.getD 876 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Alpha.Pc.q876_1 rfl).trans (powR_last CFSG.KD.Fi24Alpha.Pc.r876)))) (by quickRfl) rfl rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 879) CFSG.KD.Fi24Alpha.Pc.p877 rfl rfl)))))))).trans CFSG.KD.Fi24Alpha.Pc.f62

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v881 : Nat := CFSG.KD.Fi24Alpha.KV6 46
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v882 : Nat := CFSG.KD.Fi24Alpha.KV6 47
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l883 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v881, CFSG.KD.Fi24Alpha.Pc.v882]
theorem CFSG.KD.Fi24Alpha.Pc.p881 : Nat.beq (runC AR SD 881 (ckL CFSG.KD.Fi24Alpha.Pc.l883) 2 881 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v883 : Nat := CFSG.KD.Fi24Alpha.KV6 48
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v884 : Nat := CFSG.KD.Fi24Alpha.KV6 49
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l885 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v881, CFSG.KD.Fi24Alpha.Pc.v882, CFSG.KD.Fi24Alpha.Pc.v883, CFSG.KD.Fi24Alpha.Pc.v884]
theorem CFSG.KD.Fi24Alpha.Pc.p883 : Nat.beq (runC AR SD 881 (ckL CFSG.KD.Fi24Alpha.Pc.l885) 2 883 CFSG.KD.Fi24Alpha.Pc.l883) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v885 : Nat := CFSG.KD.Fi24Alpha.KV6 50
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v886 : Nat := CFSG.KD.Fi24Alpha.KV6 51
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l887 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v881, CFSG.KD.Fi24Alpha.Pc.v882, CFSG.KD.Fi24Alpha.Pc.v883, CFSG.KD.Fi24Alpha.Pc.v884, CFSG.KD.Fi24Alpha.Pc.v885, CFSG.KD.Fi24Alpha.Pc.v886]
theorem CFSG.KD.Fi24Alpha.Pc.p885 : Nat.beq (runC AR SD 881 (ckL CFSG.KD.Fi24Alpha.Pc.l887) 2 885 CFSG.KD.Fi24Alpha.Pc.l885) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v887 : Nat := CFSG.KD.Fi24Alpha.KV6 52
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v888 : Nat := CFSG.KD.Fi24Alpha.KV6 53
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l889 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v881, CFSG.KD.Fi24Alpha.Pc.v882, CFSG.KD.Fi24Alpha.Pc.v883, CFSG.KD.Fi24Alpha.Pc.v884, CFSG.KD.Fi24Alpha.Pc.v885, CFSG.KD.Fi24Alpha.Pc.v886, CFSG.KD.Fi24Alpha.Pc.v887, CFSG.KD.Fi24Alpha.Pc.v888]
theorem CFSG.KD.Fi24Alpha.Pc.p887 : Nat.beq (runC AR SD 881 (ckL CFSG.KD.Fi24Alpha.Pc.l889) 2 887 CFSG.KD.Fi24Alpha.Pc.l887) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v889 : Nat := CFSG.KD.Fi24Alpha.KV6 54
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v890 : Nat := CFSG.KD.Fi24Alpha.KV6 55
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l891 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v881, CFSG.KD.Fi24Alpha.Pc.v882, CFSG.KD.Fi24Alpha.Pc.v883, CFSG.KD.Fi24Alpha.Pc.v884, CFSG.KD.Fi24Alpha.Pc.v885, CFSG.KD.Fi24Alpha.Pc.v886, CFSG.KD.Fi24Alpha.Pc.v887, CFSG.KD.Fi24Alpha.Pc.v888, CFSG.KD.Fi24Alpha.Pc.v889, CFSG.KD.Fi24Alpha.Pc.v890]
theorem CFSG.KD.Fi24Alpha.Pc.p889 : Nat.beq (runC AR SD 881 (ckL CFSG.KD.Fi24Alpha.Pc.l891) 2 889 CFSG.KD.Fi24Alpha.Pc.l889) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v891 : Nat := CFSG.KD.Fi24Alpha.KV6 56
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v892 : Nat := CFSG.KD.Fi24Alpha.KV6 57
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l893 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v881, CFSG.KD.Fi24Alpha.Pc.v882, CFSG.KD.Fi24Alpha.Pc.v883, CFSG.KD.Fi24Alpha.Pc.v884, CFSG.KD.Fi24Alpha.Pc.v885, CFSG.KD.Fi24Alpha.Pc.v886, CFSG.KD.Fi24Alpha.Pc.v887, CFSG.KD.Fi24Alpha.Pc.v888, CFSG.KD.Fi24Alpha.Pc.v889, CFSG.KD.Fi24Alpha.Pc.v890, CFSG.KD.Fi24Alpha.Pc.v891, CFSG.KD.Fi24Alpha.Pc.v892]
theorem CFSG.KD.Fi24Alpha.Pc.p891 : Nat.beq (runC AR SD 881 (ckL CFSG.KD.Fi24Alpha.Pc.l893) 2 891 CFSG.KD.Fi24Alpha.Pc.l891) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v893 : Nat := CFSG.KD.Fi24Alpha.KV6 58
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v894 : Nat := CFSG.KD.Fi24Alpha.KV6 59
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l895 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v881, CFSG.KD.Fi24Alpha.Pc.v882, CFSG.KD.Fi24Alpha.Pc.v883, CFSG.KD.Fi24Alpha.Pc.v884, CFSG.KD.Fi24Alpha.Pc.v885, CFSG.KD.Fi24Alpha.Pc.v886, CFSG.KD.Fi24Alpha.Pc.v887, CFSG.KD.Fi24Alpha.Pc.v888, CFSG.KD.Fi24Alpha.Pc.v889, CFSG.KD.Fi24Alpha.Pc.v890, CFSG.KD.Fi24Alpha.Pc.v891, CFSG.KD.Fi24Alpha.Pc.v892, CFSG.KD.Fi24Alpha.Pc.v893, CFSG.KD.Fi24Alpha.Pc.v894]
theorem CFSG.KD.Fi24Alpha.Pc.p893 : Nat.beq (runC AR SD 881 (ckL CFSG.KD.Fi24Alpha.Pc.l895) 2 893 CFSG.KD.Fi24Alpha.Pc.l893) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v895 : Nat := CFSG.KD.Fi24Alpha.KV6 60
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v896 : Nat := CFSG.KD.Fi24Alpha.KV6 61
theorem CFSG.KD.Fi24Alpha.Pc.f63 : Nat.beq (runC AR SD 881 (finC AR SD (nat_lit 63) 881 897) 2 895 CFSG.KD.Fi24Alpha.Pc.l895) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk63 : chk (nat_lit 63) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 63) (lo := 881) (hi := 897) (m := 16) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 16) (m2 := 14) (j2 := 883) CFSG.KD.Fi24Alpha.Pc.p881 rfl rfl).trans ((runC_seq (m := 14) (m2 := 12) (j2 := 885) CFSG.KD.Fi24Alpha.Pc.p883 rfl rfl).trans ((runC_seq (m := 12) (m2 := 10) (j2 := 887) CFSG.KD.Fi24Alpha.Pc.p885 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 889) CFSG.KD.Fi24Alpha.Pc.p887 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 891) CFSG.KD.Fi24Alpha.Pc.p889 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 893) CFSG.KD.Fi24Alpha.Pc.p891 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 895) CFSG.KD.Fi24Alpha.Pc.p893 rfl rfl))))))))).trans CFSG.KD.Fi24Alpha.Pc.f63

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v897 : Nat := CFSG.KD.Fi24Alpha.KV6 62
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v898 : Nat := CFSG.KD.Fi24Alpha.KV6 63
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l899 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v897, CFSG.KD.Fi24Alpha.Pc.v898]
theorem CFSG.KD.Fi24Alpha.Pc.p897 : Nat.beq (runC AR SD 897 (ckL CFSG.KD.Fi24Alpha.Pc.l899) 2 897 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v899 : Nat := CFSG.KD.Fi24Alpha.KV6 64
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v900 : Nat := CFSG.KD.Fi24Alpha.KV6 65
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l901 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v897, CFSG.KD.Fi24Alpha.Pc.v898, CFSG.KD.Fi24Alpha.Pc.v899, CFSG.KD.Fi24Alpha.Pc.v900]
theorem CFSG.KD.Fi24Alpha.Pc.p899 : Nat.beq (runC AR SD 897 (ckL CFSG.KD.Fi24Alpha.Pc.l901) 2 899 CFSG.KD.Fi24Alpha.Pc.l899) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v901 : Nat := CFSG.KD.Fi24Alpha.KV6 66
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v902 : Nat := CFSG.KD.Fi24Alpha.KV6 67
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l903 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v897, CFSG.KD.Fi24Alpha.Pc.v898, CFSG.KD.Fi24Alpha.Pc.v899, CFSG.KD.Fi24Alpha.Pc.v900, CFSG.KD.Fi24Alpha.Pc.v901, CFSG.KD.Fi24Alpha.Pc.v902]
theorem CFSG.KD.Fi24Alpha.Pc.p901 : Nat.beq (runC AR SD 897 (ckL CFSG.KD.Fi24Alpha.Pc.l903) 2 901 CFSG.KD.Fi24Alpha.Pc.l901) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v903 : Nat := CFSG.KD.Fi24Alpha.KV6 68
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v904 : Nat := CFSG.KD.Fi24Alpha.KV6 69
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l905 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v897, CFSG.KD.Fi24Alpha.Pc.v898, CFSG.KD.Fi24Alpha.Pc.v899, CFSG.KD.Fi24Alpha.Pc.v900, CFSG.KD.Fi24Alpha.Pc.v901, CFSG.KD.Fi24Alpha.Pc.v902, CFSG.KD.Fi24Alpha.Pc.v903, CFSG.KD.Fi24Alpha.Pc.v904]
theorem CFSG.KD.Fi24Alpha.Pc.p903 : Nat.beq (runC AR SD 897 (ckL CFSG.KD.Fi24Alpha.Pc.l905) 2 903 CFSG.KD.Fi24Alpha.Pc.l903) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v905 : Nat := CFSG.KD.Fi24Alpha.KV6 70
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v906 : Nat := CFSG.KD.Fi24Alpha.KV6 71
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l907 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v897, CFSG.KD.Fi24Alpha.Pc.v898, CFSG.KD.Fi24Alpha.Pc.v899, CFSG.KD.Fi24Alpha.Pc.v900, CFSG.KD.Fi24Alpha.Pc.v901, CFSG.KD.Fi24Alpha.Pc.v902, CFSG.KD.Fi24Alpha.Pc.v903, CFSG.KD.Fi24Alpha.Pc.v904, CFSG.KD.Fi24Alpha.Pc.v905, CFSG.KD.Fi24Alpha.Pc.v906]
theorem CFSG.KD.Fi24Alpha.Pc.p905 : Nat.beq (runC AR SD 897 (ckL CFSG.KD.Fi24Alpha.Pc.l907) 2 905 CFSG.KD.Fi24Alpha.Pc.l905) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v907 : Nat := CFSG.KD.Fi24Alpha.KV6 72
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v908 : Nat := CFSG.KD.Fi24Alpha.KV6 73
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l909 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v897, CFSG.KD.Fi24Alpha.Pc.v898, CFSG.KD.Fi24Alpha.Pc.v899, CFSG.KD.Fi24Alpha.Pc.v900, CFSG.KD.Fi24Alpha.Pc.v901, CFSG.KD.Fi24Alpha.Pc.v902, CFSG.KD.Fi24Alpha.Pc.v903, CFSG.KD.Fi24Alpha.Pc.v904, CFSG.KD.Fi24Alpha.Pc.v905, CFSG.KD.Fi24Alpha.Pc.v906, CFSG.KD.Fi24Alpha.Pc.v907, CFSG.KD.Fi24Alpha.Pc.v908]
theorem CFSG.KD.Fi24Alpha.Pc.p907 : Nat.beq (runC AR SD 897 (ckL CFSG.KD.Fi24Alpha.Pc.l909) 2 907 CFSG.KD.Fi24Alpha.Pc.l907) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v909 : Nat := CFSG.KD.Fi24Alpha.KV6 74
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v910 : Nat := CFSG.KD.Fi24Alpha.KV6 75
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l911 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v897, CFSG.KD.Fi24Alpha.Pc.v898, CFSG.KD.Fi24Alpha.Pc.v899, CFSG.KD.Fi24Alpha.Pc.v900, CFSG.KD.Fi24Alpha.Pc.v901, CFSG.KD.Fi24Alpha.Pc.v902, CFSG.KD.Fi24Alpha.Pc.v903, CFSG.KD.Fi24Alpha.Pc.v904, CFSG.KD.Fi24Alpha.Pc.v905, CFSG.KD.Fi24Alpha.Pc.v906, CFSG.KD.Fi24Alpha.Pc.v907, CFSG.KD.Fi24Alpha.Pc.v908, CFSG.KD.Fi24Alpha.Pc.v909, CFSG.KD.Fi24Alpha.Pc.v910]
theorem CFSG.KD.Fi24Alpha.Pc.p909 : Nat.beq (runC AR SD 897 (ckL CFSG.KD.Fi24Alpha.Pc.l911) 2 909 CFSG.KD.Fi24Alpha.Pc.l909) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v911 : Nat := CFSG.KD.Fi24Alpha.KV6 76
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v912 : Nat := CFSG.KD.Fi24Alpha.KV6 77
theorem CFSG.KD.Fi24Alpha.Pc.f64 : Nat.beq (runC AR SD 897 (finC AR SD (nat_lit 64) 897 913) 2 911 CFSG.KD.Fi24Alpha.Pc.l911) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk64 : chk (nat_lit 64) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 64) (lo := 897) (hi := 913) (m := 16) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 16) (m2 := 14) (j2 := 899) CFSG.KD.Fi24Alpha.Pc.p897 rfl rfl).trans ((runC_seq (m := 14) (m2 := 12) (j2 := 901) CFSG.KD.Fi24Alpha.Pc.p899 rfl rfl).trans ((runC_seq (m := 12) (m2 := 10) (j2 := 903) CFSG.KD.Fi24Alpha.Pc.p901 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 905) CFSG.KD.Fi24Alpha.Pc.p903 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 907) CFSG.KD.Fi24Alpha.Pc.p905 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 909) CFSG.KD.Fi24Alpha.Pc.p907 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 911) CFSG.KD.Fi24Alpha.Pc.p909 rfl rfl))))))))).trans CFSG.KD.Fi24Alpha.Pc.f64

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v913 : Nat := CFSG.KD.Fi24Alpha.KV6 78
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v914 : Nat := CFSG.KD.Fi24Alpha.KV6 79
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l915 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v913, CFSG.KD.Fi24Alpha.Pc.v914]
theorem CFSG.KD.Fi24Alpha.Pc.p913 : Nat.beq (runC AR SD 913 (ckL CFSG.KD.Fi24Alpha.Pc.l915) 2 913 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v915 : Nat := CFSG.KD.Fi24Alpha.KV6 80
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v916 : Nat := CFSG.KD.Fi24Alpha.KV6 81
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l917 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v913, CFSG.KD.Fi24Alpha.Pc.v914, CFSG.KD.Fi24Alpha.Pc.v915, CFSG.KD.Fi24Alpha.Pc.v916]
theorem CFSG.KD.Fi24Alpha.Pc.p915 : Nat.beq (runC AR SD 913 (ckL CFSG.KD.Fi24Alpha.Pc.l917) 2 915 CFSG.KD.Fi24Alpha.Pc.l915) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v917 : Nat := CFSG.KD.Fi24Alpha.KV6 82
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v918 : Nat := CFSG.KD.Fi24Alpha.KV6 83
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l919 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v913, CFSG.KD.Fi24Alpha.Pc.v914, CFSG.KD.Fi24Alpha.Pc.v915, CFSG.KD.Fi24Alpha.Pc.v916, CFSG.KD.Fi24Alpha.Pc.v917, CFSG.KD.Fi24Alpha.Pc.v918]
theorem CFSG.KD.Fi24Alpha.Pc.p917 : Nat.beq (runC AR SD 913 (ckL CFSG.KD.Fi24Alpha.Pc.l919) 2 917 CFSG.KD.Fi24Alpha.Pc.l917) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v919 : Nat := CFSG.KD.Fi24Alpha.KV6 84
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v920 : Nat := CFSG.KD.Fi24Alpha.KV6 85
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l921 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v913, CFSG.KD.Fi24Alpha.Pc.v914, CFSG.KD.Fi24Alpha.Pc.v915, CFSG.KD.Fi24Alpha.Pc.v916, CFSG.KD.Fi24Alpha.Pc.v917, CFSG.KD.Fi24Alpha.Pc.v918, CFSG.KD.Fi24Alpha.Pc.v919, CFSG.KD.Fi24Alpha.Pc.v920]
theorem CFSG.KD.Fi24Alpha.Pc.p919 : Nat.beq (runC AR SD 913 (ckL CFSG.KD.Fi24Alpha.Pc.l921) 2 919 CFSG.KD.Fi24Alpha.Pc.l919) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v921 : Nat := CFSG.KD.Fi24Alpha.KV6 86
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v922 : Nat := CFSG.KD.Fi24Alpha.KV6 87
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l923 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v913, CFSG.KD.Fi24Alpha.Pc.v914, CFSG.KD.Fi24Alpha.Pc.v915, CFSG.KD.Fi24Alpha.Pc.v916, CFSG.KD.Fi24Alpha.Pc.v917, CFSG.KD.Fi24Alpha.Pc.v918, CFSG.KD.Fi24Alpha.Pc.v919, CFSG.KD.Fi24Alpha.Pc.v920, CFSG.KD.Fi24Alpha.Pc.v921, CFSG.KD.Fi24Alpha.Pc.v922]
theorem CFSG.KD.Fi24Alpha.Pc.p921 : Nat.beq (runC AR SD 913 (ckL CFSG.KD.Fi24Alpha.Pc.l923) 2 921 CFSG.KD.Fi24Alpha.Pc.l921) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v923 : Nat := CFSG.KD.Fi24Alpha.KV6 88
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v924 : Nat := CFSG.KD.Fi24Alpha.KV6 89
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l925 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v913, CFSG.KD.Fi24Alpha.Pc.v914, CFSG.KD.Fi24Alpha.Pc.v915, CFSG.KD.Fi24Alpha.Pc.v916, CFSG.KD.Fi24Alpha.Pc.v917, CFSG.KD.Fi24Alpha.Pc.v918, CFSG.KD.Fi24Alpha.Pc.v919, CFSG.KD.Fi24Alpha.Pc.v920, CFSG.KD.Fi24Alpha.Pc.v921, CFSG.KD.Fi24Alpha.Pc.v922, CFSG.KD.Fi24Alpha.Pc.v923, CFSG.KD.Fi24Alpha.Pc.v924]
theorem CFSG.KD.Fi24Alpha.Pc.p923 : Nat.beq (runC AR SD 913 (ckL CFSG.KD.Fi24Alpha.Pc.l925) 2 923 CFSG.KD.Fi24Alpha.Pc.l923) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v925 : Nat := CFSG.KD.Fi24Alpha.KV6 90
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v926 : Nat := CFSG.KD.Fi24Alpha.KV6 91
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l927 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v913, CFSG.KD.Fi24Alpha.Pc.v914, CFSG.KD.Fi24Alpha.Pc.v915, CFSG.KD.Fi24Alpha.Pc.v916, CFSG.KD.Fi24Alpha.Pc.v917, CFSG.KD.Fi24Alpha.Pc.v918, CFSG.KD.Fi24Alpha.Pc.v919, CFSG.KD.Fi24Alpha.Pc.v920, CFSG.KD.Fi24Alpha.Pc.v921, CFSG.KD.Fi24Alpha.Pc.v922, CFSG.KD.Fi24Alpha.Pc.v923, CFSG.KD.Fi24Alpha.Pc.v924, CFSG.KD.Fi24Alpha.Pc.v925, CFSG.KD.Fi24Alpha.Pc.v926]
theorem CFSG.KD.Fi24Alpha.Pc.p925 : Nat.beq (runC AR SD 913 (ckL CFSG.KD.Fi24Alpha.Pc.l927) 2 925 CFSG.KD.Fi24Alpha.Pc.l925) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v927 : Nat := CFSG.KD.Fi24Alpha.KV6 92
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v928 : Nat := CFSG.KD.Fi24Alpha.KV6 93
theorem CFSG.KD.Fi24Alpha.Pc.f65 : Nat.beq (runC AR SD 913 (finC AR SD (nat_lit 65) 913 929) 2 927 CFSG.KD.Fi24Alpha.Pc.l927) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk65 : chk (nat_lit 65) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 65) (lo := 913) (hi := 929) (m := 16) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 16) (m2 := 14) (j2 := 915) CFSG.KD.Fi24Alpha.Pc.p913 rfl rfl).trans ((runC_seq (m := 14) (m2 := 12) (j2 := 917) CFSG.KD.Fi24Alpha.Pc.p915 rfl rfl).trans ((runC_seq (m := 12) (m2 := 10) (j2 := 919) CFSG.KD.Fi24Alpha.Pc.p917 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 921) CFSG.KD.Fi24Alpha.Pc.p919 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 923) CFSG.KD.Fi24Alpha.Pc.p921 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 925) CFSG.KD.Fi24Alpha.Pc.p923 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 927) CFSG.KD.Fi24Alpha.Pc.p925 rfl rfl))))))))).trans CFSG.KD.Fi24Alpha.Pc.f65

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v929 : Nat := CFSG.KD.Fi24Alpha.KV6 94
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v930 : Nat := CFSG.KD.Fi24Alpha.KV6 95
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l931 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v929, CFSG.KD.Fi24Alpha.Pc.v930]
theorem CFSG.KD.Fi24Alpha.Pc.p929 : Nat.beq (runC AR SD 929 (ckL CFSG.KD.Fi24Alpha.Pc.l931) 2 929 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v931 : Nat := CFSG.KD.Fi24Alpha.KV6 96
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v932 : Nat := CFSG.KD.Fi24Alpha.KV6 97
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l933 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v929, CFSG.KD.Fi24Alpha.Pc.v930, CFSG.KD.Fi24Alpha.Pc.v931, CFSG.KD.Fi24Alpha.Pc.v932]
theorem CFSG.KD.Fi24Alpha.Pc.p931 : Nat.beq (runC AR SD 929 (ckL CFSG.KD.Fi24Alpha.Pc.l933) 2 931 CFSG.KD.Fi24Alpha.Pc.l931) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v933 : Nat := CFSG.KD.Fi24Alpha.KV6 98
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l934 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v929, CFSG.KD.Fi24Alpha.Pc.v930, CFSG.KD.Fi24Alpha.Pc.v931, CFSG.KD.Fi24Alpha.Pc.v932, CFSG.KD.Fi24Alpha.Pc.v933]
theorem CFSG.KD.Fi24Alpha.Pc.p933 : Nat.beq (runC AR SD 929 (ckL CFSG.KD.Fi24Alpha.Pc.l934) 1 933 CFSG.KD.Fi24Alpha.Pc.l933) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v934 : Nat := CFSG.KD.Fi24Alpha.KV6 99
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l935 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v929, CFSG.KD.Fi24Alpha.Pc.v930, CFSG.KD.Fi24Alpha.Pc.v931, CFSG.KD.Fi24Alpha.Pc.v932, CFSG.KD.Fi24Alpha.Pc.v933, CFSG.KD.Fi24Alpha.Pc.v934]
theorem CFSG.KD.Fi24Alpha.Pc.p934 : Nat.beq (runC AR SD 929 (ckL CFSG.KD.Fi24Alpha.Pc.l935) 1 934 CFSG.KD.Fi24Alpha.Pc.l934) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v935 : Nat := CFSG.KD.Fi24Alpha.KV6 100
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v936 : Nat := CFSG.KD.Fi24Alpha.KV6 101
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l937 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v929, CFSG.KD.Fi24Alpha.Pc.v930, CFSG.KD.Fi24Alpha.Pc.v931, CFSG.KD.Fi24Alpha.Pc.v932, CFSG.KD.Fi24Alpha.Pc.v933, CFSG.KD.Fi24Alpha.Pc.v934, CFSG.KD.Fi24Alpha.Pc.v935, CFSG.KD.Fi24Alpha.Pc.v936]
theorem CFSG.KD.Fi24Alpha.Pc.p935 : Nat.beq (runC AR SD 929 (ckL CFSG.KD.Fi24Alpha.Pc.l937) 2 935 CFSG.KD.Fi24Alpha.Pc.l935) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v937 : Nat := CFSG.KD.Fi24Alpha.KV6 102
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v938 : Nat := CFSG.KD.Fi24Alpha.KV6 103
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l939 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v929, CFSG.KD.Fi24Alpha.Pc.v930, CFSG.KD.Fi24Alpha.Pc.v931, CFSG.KD.Fi24Alpha.Pc.v932, CFSG.KD.Fi24Alpha.Pc.v933, CFSG.KD.Fi24Alpha.Pc.v934, CFSG.KD.Fi24Alpha.Pc.v935, CFSG.KD.Fi24Alpha.Pc.v936, CFSG.KD.Fi24Alpha.Pc.v937, CFSG.KD.Fi24Alpha.Pc.v938]
theorem CFSG.KD.Fi24Alpha.Pc.p937 : Nat.beq (runC AR SD 929 (ckL CFSG.KD.Fi24Alpha.Pc.l939) 2 937 CFSG.KD.Fi24Alpha.Pc.l937) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v939 : Nat := CFSG.KD.Fi24Alpha.KV6 104
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v940 : Nat := CFSG.KD.Fi24Alpha.KV6 105
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l941 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v929, CFSG.KD.Fi24Alpha.Pc.v930, CFSG.KD.Fi24Alpha.Pc.v931, CFSG.KD.Fi24Alpha.Pc.v932, CFSG.KD.Fi24Alpha.Pc.v933, CFSG.KD.Fi24Alpha.Pc.v934, CFSG.KD.Fi24Alpha.Pc.v935, CFSG.KD.Fi24Alpha.Pc.v936, CFSG.KD.Fi24Alpha.Pc.v937, CFSG.KD.Fi24Alpha.Pc.v938, CFSG.KD.Fi24Alpha.Pc.v939, CFSG.KD.Fi24Alpha.Pc.v940]
theorem CFSG.KD.Fi24Alpha.Pc.p939 : Nat.beq (runC AR SD 929 (ckL CFSG.KD.Fi24Alpha.Pc.l941) 2 939 CFSG.KD.Fi24Alpha.Pc.l939) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v941 : Nat := CFSG.KD.Fi24Alpha.KV6 106
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v942 : Nat := CFSG.KD.Fi24Alpha.KV6 107
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l943 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v929, CFSG.KD.Fi24Alpha.Pc.v930, CFSG.KD.Fi24Alpha.Pc.v931, CFSG.KD.Fi24Alpha.Pc.v932, CFSG.KD.Fi24Alpha.Pc.v933, CFSG.KD.Fi24Alpha.Pc.v934, CFSG.KD.Fi24Alpha.Pc.v935, CFSG.KD.Fi24Alpha.Pc.v936, CFSG.KD.Fi24Alpha.Pc.v937, CFSG.KD.Fi24Alpha.Pc.v938, CFSG.KD.Fi24Alpha.Pc.v939, CFSG.KD.Fi24Alpha.Pc.v940, CFSG.KD.Fi24Alpha.Pc.v941, CFSG.KD.Fi24Alpha.Pc.v942]
theorem CFSG.KD.Fi24Alpha.Pc.p941 : Nat.beq (runC AR SD 929 (ckL CFSG.KD.Fi24Alpha.Pc.l943) 2 941 CFSG.KD.Fi24Alpha.Pc.l941) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v943 : Nat := CFSG.KD.Fi24Alpha.KV6 108
theorem CFSG.KD.Fi24Alpha.Pc.f66 : Nat.beq (runC AR SD 929 (finC AR SD (nat_lit 66) 929 944) 1 943 CFSG.KD.Fi24Alpha.Pc.l943) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk66 : chk (nat_lit 66) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 66) (lo := 929) (hi := 944) (m := 15) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 15) (m2 := 13) (j2 := 931) CFSG.KD.Fi24Alpha.Pc.p929 rfl rfl).trans ((runC_seq (m := 13) (m2 := 11) (j2 := 933) CFSG.KD.Fi24Alpha.Pc.p931 rfl rfl).trans ((runC_seq (m := 11) (m2 := 10) (j2 := 934) CFSG.KD.Fi24Alpha.Pc.p933 rfl rfl).trans ((runC_seq (m := 10) (m2 := 9) (j2 := 935) CFSG.KD.Fi24Alpha.Pc.p934 rfl rfl).trans ((runC_seq (m := 9) (m2 := 7) (j2 := 937) CFSG.KD.Fi24Alpha.Pc.p935 rfl rfl).trans ((runC_seq (m := 7) (m2 := 5) (j2 := 939) CFSG.KD.Fi24Alpha.Pc.p937 rfl rfl).trans ((runC_seq (m := 5) (m2 := 3) (j2 := 941) CFSG.KD.Fi24Alpha.Pc.p939 rfl rfl).trans (runC_seq (m := 3) (m2 := 1) (j2 := 943) CFSG.KD.Fi24Alpha.Pc.p941 rfl rfl)))))))))).trans CFSG.KD.Fi24Alpha.Pc.f66

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v944 : Nat := CFSG.KD.Fi24Alpha.KV6 109
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v945 : Nat := CFSG.KD.Fi24Alpha.KV6 110
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l946 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v944, CFSG.KD.Fi24Alpha.Pc.v945]
theorem CFSG.KD.Fi24Alpha.Pc.p944 : Nat.beq (runC AR SD 944 (ckL CFSG.KD.Fi24Alpha.Pc.l946) 2 944 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v946 : Nat := CFSG.KD.Fi24Alpha.KV6 111
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v947 : Nat := CFSG.KD.Fi24Alpha.KV6 112
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l948 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v944, CFSG.KD.Fi24Alpha.Pc.v945, CFSG.KD.Fi24Alpha.Pc.v946, CFSG.KD.Fi24Alpha.Pc.v947]
theorem CFSG.KD.Fi24Alpha.Pc.p946 : Nat.beq (runC AR SD 944 (ckL CFSG.KD.Fi24Alpha.Pc.l948) 2 946 CFSG.KD.Fi24Alpha.Pc.l946) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v948 : Nat := CFSG.KD.Fi24Alpha.KV6 113
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v949 : Nat := CFSG.KD.Fi24Alpha.KV6 114
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l950 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v944, CFSG.KD.Fi24Alpha.Pc.v945, CFSG.KD.Fi24Alpha.Pc.v946, CFSG.KD.Fi24Alpha.Pc.v947, CFSG.KD.Fi24Alpha.Pc.v948, CFSG.KD.Fi24Alpha.Pc.v949]
theorem CFSG.KD.Fi24Alpha.Pc.p948 : Nat.beq (runC AR SD 944 (ckL CFSG.KD.Fi24Alpha.Pc.l950) 2 948 CFSG.KD.Fi24Alpha.Pc.l948) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v950 : Nat := CFSG.KD.Fi24Alpha.KV6 115
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v951 : Nat := CFSG.KD.Fi24Alpha.KV6 116
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l952 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v944, CFSG.KD.Fi24Alpha.Pc.v945, CFSG.KD.Fi24Alpha.Pc.v946, CFSG.KD.Fi24Alpha.Pc.v947, CFSG.KD.Fi24Alpha.Pc.v948, CFSG.KD.Fi24Alpha.Pc.v949, CFSG.KD.Fi24Alpha.Pc.v950, CFSG.KD.Fi24Alpha.Pc.v951]
theorem CFSG.KD.Fi24Alpha.Pc.p950 : Nat.beq (runC AR SD 944 (ckL CFSG.KD.Fi24Alpha.Pc.l952) 2 950 CFSG.KD.Fi24Alpha.Pc.l950) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v952 : Nat := CFSG.KD.Fi24Alpha.KV6 117
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v953 : Nat := CFSG.KD.Fi24Alpha.KV6 118
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l954 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v944, CFSG.KD.Fi24Alpha.Pc.v945, CFSG.KD.Fi24Alpha.Pc.v946, CFSG.KD.Fi24Alpha.Pc.v947, CFSG.KD.Fi24Alpha.Pc.v948, CFSG.KD.Fi24Alpha.Pc.v949, CFSG.KD.Fi24Alpha.Pc.v950, CFSG.KD.Fi24Alpha.Pc.v951, CFSG.KD.Fi24Alpha.Pc.v952, CFSG.KD.Fi24Alpha.Pc.v953]
theorem CFSG.KD.Fi24Alpha.Pc.p952 : Nat.beq (runC AR SD 944 (ckL CFSG.KD.Fi24Alpha.Pc.l954) 2 952 CFSG.KD.Fi24Alpha.Pc.l952) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v954 : Nat := CFSG.KD.Fi24Alpha.KV6 119
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v955 : Nat := CFSG.KD.Fi24Alpha.KV6 120
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l956 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v944, CFSG.KD.Fi24Alpha.Pc.v945, CFSG.KD.Fi24Alpha.Pc.v946, CFSG.KD.Fi24Alpha.Pc.v947, CFSG.KD.Fi24Alpha.Pc.v948, CFSG.KD.Fi24Alpha.Pc.v949, CFSG.KD.Fi24Alpha.Pc.v950, CFSG.KD.Fi24Alpha.Pc.v951, CFSG.KD.Fi24Alpha.Pc.v952, CFSG.KD.Fi24Alpha.Pc.v953, CFSG.KD.Fi24Alpha.Pc.v954, CFSG.KD.Fi24Alpha.Pc.v955]
theorem CFSG.KD.Fi24Alpha.Pc.p954 : Nat.beq (runC AR SD 944 (ckL CFSG.KD.Fi24Alpha.Pc.l956) 2 954 CFSG.KD.Fi24Alpha.Pc.l954) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v956 : Nat := CFSG.KD.Fi24Alpha.KV6 121
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v957 : Nat := CFSG.KD.Fi24Alpha.KV6 122
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l958 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v944, CFSG.KD.Fi24Alpha.Pc.v945, CFSG.KD.Fi24Alpha.Pc.v946, CFSG.KD.Fi24Alpha.Pc.v947, CFSG.KD.Fi24Alpha.Pc.v948, CFSG.KD.Fi24Alpha.Pc.v949, CFSG.KD.Fi24Alpha.Pc.v950, CFSG.KD.Fi24Alpha.Pc.v951, CFSG.KD.Fi24Alpha.Pc.v952, CFSG.KD.Fi24Alpha.Pc.v953, CFSG.KD.Fi24Alpha.Pc.v954, CFSG.KD.Fi24Alpha.Pc.v955, CFSG.KD.Fi24Alpha.Pc.v956, CFSG.KD.Fi24Alpha.Pc.v957]
theorem CFSG.KD.Fi24Alpha.Pc.p956 : Nat.beq (runC AR SD 944 (ckL CFSG.KD.Fi24Alpha.Pc.l958) 2 956 CFSG.KD.Fi24Alpha.Pc.l956) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v958 : Nat := CFSG.KD.Fi24Alpha.KV6 123
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v959 : Nat := CFSG.KD.Fi24Alpha.KV6 124
theorem CFSG.KD.Fi24Alpha.Pc.f67 : Nat.beq (runC AR SD 944 (finC AR SD (nat_lit 67) 944 960) 2 958 CFSG.KD.Fi24Alpha.Pc.l958) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk67 : chk (nat_lit 67) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 67) (lo := 944) (hi := 960) (m := 16) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 16) (m2 := 14) (j2 := 946) CFSG.KD.Fi24Alpha.Pc.p944 rfl rfl).trans ((runC_seq (m := 14) (m2 := 12) (j2 := 948) CFSG.KD.Fi24Alpha.Pc.p946 rfl rfl).trans ((runC_seq (m := 12) (m2 := 10) (j2 := 950) CFSG.KD.Fi24Alpha.Pc.p948 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 952) CFSG.KD.Fi24Alpha.Pc.p950 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 954) CFSG.KD.Fi24Alpha.Pc.p952 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 956) CFSG.KD.Fi24Alpha.Pc.p954 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 958) CFSG.KD.Fi24Alpha.Pc.p956 rfl rfl))))))))).trans CFSG.KD.Fi24Alpha.Pc.f67

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v960 : Nat := CFSG.KD.Fi24Alpha.KV6 125
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v961 : Nat := CFSG.KD.Fi24Alpha.KV6 126
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l962 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v960, CFSG.KD.Fi24Alpha.Pc.v961]
theorem CFSG.KD.Fi24Alpha.Pc.p960 : Nat.beq (runC AR SD 960 (ckL CFSG.KD.Fi24Alpha.Pc.l962) 2 960 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v962 : Nat := CFSG.KD.Fi24Alpha.KV6 127
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v963 : Nat := CFSG.KD.Fi24Alpha.KV6 128
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l964 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v960, CFSG.KD.Fi24Alpha.Pc.v961, CFSG.KD.Fi24Alpha.Pc.v962, CFSG.KD.Fi24Alpha.Pc.v963]
theorem CFSG.KD.Fi24Alpha.Pc.p962 : Nat.beq (runC AR SD 960 (ckL CFSG.KD.Fi24Alpha.Pc.l964) 2 962 CFSG.KD.Fi24Alpha.Pc.l962) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v964 : Nat := CFSG.KD.Fi24Alpha.KV6 129
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v965 : Nat := CFSG.KD.Fi24Alpha.KV6 130
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l966 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v960, CFSG.KD.Fi24Alpha.Pc.v961, CFSG.KD.Fi24Alpha.Pc.v962, CFSG.KD.Fi24Alpha.Pc.v963, CFSG.KD.Fi24Alpha.Pc.v964, CFSG.KD.Fi24Alpha.Pc.v965]
theorem CFSG.KD.Fi24Alpha.Pc.p964 : Nat.beq (runC AR SD 960 (ckL CFSG.KD.Fi24Alpha.Pc.l966) 2 964 CFSG.KD.Fi24Alpha.Pc.l964) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v966 : Nat := CFSG.KD.Fi24Alpha.KV6 131
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v967 : Nat := CFSG.KD.Fi24Alpha.KV6 132
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l968 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v960, CFSG.KD.Fi24Alpha.Pc.v961, CFSG.KD.Fi24Alpha.Pc.v962, CFSG.KD.Fi24Alpha.Pc.v963, CFSG.KD.Fi24Alpha.Pc.v964, CFSG.KD.Fi24Alpha.Pc.v965, CFSG.KD.Fi24Alpha.Pc.v966, CFSG.KD.Fi24Alpha.Pc.v967]
theorem CFSG.KD.Fi24Alpha.Pc.p966 : Nat.beq (runC AR SD 960 (ckL CFSG.KD.Fi24Alpha.Pc.l968) 2 966 CFSG.KD.Fi24Alpha.Pc.l966) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v968 : Nat := CFSG.KD.Fi24Alpha.KV6 133
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v969 : Nat := CFSG.KD.Fi24Alpha.KV6 134
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l970 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v960, CFSG.KD.Fi24Alpha.Pc.v961, CFSG.KD.Fi24Alpha.Pc.v962, CFSG.KD.Fi24Alpha.Pc.v963, CFSG.KD.Fi24Alpha.Pc.v964, CFSG.KD.Fi24Alpha.Pc.v965, CFSG.KD.Fi24Alpha.Pc.v966, CFSG.KD.Fi24Alpha.Pc.v967, CFSG.KD.Fi24Alpha.Pc.v968, CFSG.KD.Fi24Alpha.Pc.v969]
theorem CFSG.KD.Fi24Alpha.Pc.p968 : Nat.beq (runC AR SD 960 (ckL CFSG.KD.Fi24Alpha.Pc.l970) 2 968 CFSG.KD.Fi24Alpha.Pc.l968) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v970 : Nat := CFSG.KD.Fi24Alpha.KV6 135
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v971 : Nat := CFSG.KD.Fi24Alpha.KV6 136
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l972 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v960, CFSG.KD.Fi24Alpha.Pc.v961, CFSG.KD.Fi24Alpha.Pc.v962, CFSG.KD.Fi24Alpha.Pc.v963, CFSG.KD.Fi24Alpha.Pc.v964, CFSG.KD.Fi24Alpha.Pc.v965, CFSG.KD.Fi24Alpha.Pc.v966, CFSG.KD.Fi24Alpha.Pc.v967, CFSG.KD.Fi24Alpha.Pc.v968, CFSG.KD.Fi24Alpha.Pc.v969, CFSG.KD.Fi24Alpha.Pc.v970, CFSG.KD.Fi24Alpha.Pc.v971]
theorem CFSG.KD.Fi24Alpha.Pc.p970 : Nat.beq (runC AR SD 960 (ckL CFSG.KD.Fi24Alpha.Pc.l972) 2 970 CFSG.KD.Fi24Alpha.Pc.l970) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v972 : Nat := CFSG.KD.Fi24Alpha.KV6 137
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v973 : Nat := CFSG.KD.Fi24Alpha.KV6 138
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l974 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v960, CFSG.KD.Fi24Alpha.Pc.v961, CFSG.KD.Fi24Alpha.Pc.v962, CFSG.KD.Fi24Alpha.Pc.v963, CFSG.KD.Fi24Alpha.Pc.v964, CFSG.KD.Fi24Alpha.Pc.v965, CFSG.KD.Fi24Alpha.Pc.v966, CFSG.KD.Fi24Alpha.Pc.v967, CFSG.KD.Fi24Alpha.Pc.v968, CFSG.KD.Fi24Alpha.Pc.v969, CFSG.KD.Fi24Alpha.Pc.v970, CFSG.KD.Fi24Alpha.Pc.v971, CFSG.KD.Fi24Alpha.Pc.v972, CFSG.KD.Fi24Alpha.Pc.v973]
theorem CFSG.KD.Fi24Alpha.Pc.p972 : Nat.beq (runC AR SD 960 (ckL CFSG.KD.Fi24Alpha.Pc.l974) 2 972 CFSG.KD.Fi24Alpha.Pc.l972) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v974 : Nat := CFSG.KD.Fi24Alpha.KV6 139
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v975 : Nat := CFSG.KD.Fi24Alpha.KV6 140
theorem CFSG.KD.Fi24Alpha.Pc.f68 : Nat.beq (runC AR SD 960 (finC AR SD (nat_lit 68) 960 976) 2 974 CFSG.KD.Fi24Alpha.Pc.l974) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk68 : chk (nat_lit 68) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 68) (lo := 960) (hi := 976) (m := 16) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 16) (m2 := 14) (j2 := 962) CFSG.KD.Fi24Alpha.Pc.p960 rfl rfl).trans ((runC_seq (m := 14) (m2 := 12) (j2 := 964) CFSG.KD.Fi24Alpha.Pc.p962 rfl rfl).trans ((runC_seq (m := 12) (m2 := 10) (j2 := 966) CFSG.KD.Fi24Alpha.Pc.p964 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 968) CFSG.KD.Fi24Alpha.Pc.p966 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 970) CFSG.KD.Fi24Alpha.Pc.p968 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 972) CFSG.KD.Fi24Alpha.Pc.p970 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 974) CFSG.KD.Fi24Alpha.Pc.p972 rfl rfl))))))))).trans CFSG.KD.Fi24Alpha.Pc.f68

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v976 : Nat := CFSG.KD.Fi24Alpha.KV6 141
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l977 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v976]
theorem CFSG.KD.Fi24Alpha.Pc.p976 : Nat.beq (runC AR SD 976 (ckL CFSG.KD.Fi24Alpha.Pc.l977) 1 976 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v977 : Nat := CFSG.KD.Fi24Alpha.KV6 142
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l978 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v976, CFSG.KD.Fi24Alpha.Pc.v977]
theorem CFSG.KD.Fi24Alpha.Pc.p977 : Nat.beq (runC AR SD 976 (ckL CFSG.KD.Fi24Alpha.Pc.l978) 1 977 CFSG.KD.Fi24Alpha.Pc.l977) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v978 : Nat := CFSG.KD.Fi24Alpha.KV6 143
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v979 : Nat := CFSG.KD.Fi24Alpha.KV6 144
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l980 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v976, CFSG.KD.Fi24Alpha.Pc.v977, CFSG.KD.Fi24Alpha.Pc.v978, CFSG.KD.Fi24Alpha.Pc.v979]
theorem CFSG.KD.Fi24Alpha.Pc.p978 : Nat.beq (runC AR SD 976 (ckL CFSG.KD.Fi24Alpha.Pc.l980) 2 978 CFSG.KD.Fi24Alpha.Pc.l978) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v980 : Nat := CFSG.KD.Fi24Alpha.KV6 145
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v981 : Nat := CFSG.KD.Fi24Alpha.KV6 146
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l982 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v976, CFSG.KD.Fi24Alpha.Pc.v977, CFSG.KD.Fi24Alpha.Pc.v978, CFSG.KD.Fi24Alpha.Pc.v979, CFSG.KD.Fi24Alpha.Pc.v980, CFSG.KD.Fi24Alpha.Pc.v981]
theorem CFSG.KD.Fi24Alpha.Pc.p980 : Nat.beq (runC AR SD 976 (ckL CFSG.KD.Fi24Alpha.Pc.l982) 2 980 CFSG.KD.Fi24Alpha.Pc.l980) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v982 : Nat := CFSG.KD.Fi24Alpha.KV6 147
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v983 : Nat := CFSG.KD.Fi24Alpha.KV6 148
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l984 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v976, CFSG.KD.Fi24Alpha.Pc.v977, CFSG.KD.Fi24Alpha.Pc.v978, CFSG.KD.Fi24Alpha.Pc.v979, CFSG.KD.Fi24Alpha.Pc.v980, CFSG.KD.Fi24Alpha.Pc.v981, CFSG.KD.Fi24Alpha.Pc.v982, CFSG.KD.Fi24Alpha.Pc.v983]
theorem CFSG.KD.Fi24Alpha.Pc.p982 : Nat.beq (runC AR SD 976 (ckL CFSG.KD.Fi24Alpha.Pc.l984) 2 982 CFSG.KD.Fi24Alpha.Pc.l982) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v984 : Nat := CFSG.KD.Fi24Alpha.KV6 149
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v985 : Nat := CFSG.KD.Fi24Alpha.KV6 150
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l986 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v976, CFSG.KD.Fi24Alpha.Pc.v977, CFSG.KD.Fi24Alpha.Pc.v978, CFSG.KD.Fi24Alpha.Pc.v979, CFSG.KD.Fi24Alpha.Pc.v980, CFSG.KD.Fi24Alpha.Pc.v981, CFSG.KD.Fi24Alpha.Pc.v982, CFSG.KD.Fi24Alpha.Pc.v983, CFSG.KD.Fi24Alpha.Pc.v984, CFSG.KD.Fi24Alpha.Pc.v985]
theorem CFSG.KD.Fi24Alpha.Pc.p984 : Nat.beq (runC AR SD 976 (ckL CFSG.KD.Fi24Alpha.Pc.l986) 2 984 CFSG.KD.Fi24Alpha.Pc.l984) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v986 : Nat := CFSG.KD.Fi24Alpha.KV6 151
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v987 : Nat := CFSG.KD.Fi24Alpha.KV6 152
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l988 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v976, CFSG.KD.Fi24Alpha.Pc.v977, CFSG.KD.Fi24Alpha.Pc.v978, CFSG.KD.Fi24Alpha.Pc.v979, CFSG.KD.Fi24Alpha.Pc.v980, CFSG.KD.Fi24Alpha.Pc.v981, CFSG.KD.Fi24Alpha.Pc.v982, CFSG.KD.Fi24Alpha.Pc.v983, CFSG.KD.Fi24Alpha.Pc.v984, CFSG.KD.Fi24Alpha.Pc.v985, CFSG.KD.Fi24Alpha.Pc.v986, CFSG.KD.Fi24Alpha.Pc.v987]
theorem CFSG.KD.Fi24Alpha.Pc.p986 : Nat.beq (runC AR SD 976 (ckL CFSG.KD.Fi24Alpha.Pc.l988) 2 986 CFSG.KD.Fi24Alpha.Pc.l986) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v988 : Nat := CFSG.KD.Fi24Alpha.KV6 153
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v989 : Nat := CFSG.KD.Fi24Alpha.KV6 154
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l990 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v976, CFSG.KD.Fi24Alpha.Pc.v977, CFSG.KD.Fi24Alpha.Pc.v978, CFSG.KD.Fi24Alpha.Pc.v979, CFSG.KD.Fi24Alpha.Pc.v980, CFSG.KD.Fi24Alpha.Pc.v981, CFSG.KD.Fi24Alpha.Pc.v982, CFSG.KD.Fi24Alpha.Pc.v983, CFSG.KD.Fi24Alpha.Pc.v984, CFSG.KD.Fi24Alpha.Pc.v985, CFSG.KD.Fi24Alpha.Pc.v986, CFSG.KD.Fi24Alpha.Pc.v987, CFSG.KD.Fi24Alpha.Pc.v988, CFSG.KD.Fi24Alpha.Pc.v989]
theorem CFSG.KD.Fi24Alpha.Pc.p988 : Nat.beq (runC AR SD 976 (ckL CFSG.KD.Fi24Alpha.Pc.l990) 2 988 CFSG.KD.Fi24Alpha.Pc.l988) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v990 : Nat := CFSG.KD.Fi24Alpha.KV6 155
theorem CFSG.KD.Fi24Alpha.Pc.f69 : Nat.beq (runC AR SD 976 (finC AR SD (nat_lit 69) 976 991) 1 990 CFSG.KD.Fi24Alpha.Pc.l990) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk69 : chk (nat_lit 69) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 69) (lo := 976) (hi := 991) (m := 15) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 15) (m2 := 14) (j2 := 977) CFSG.KD.Fi24Alpha.Pc.p976 rfl rfl).trans ((runC_seq (m := 14) (m2 := 13) (j2 := 978) CFSG.KD.Fi24Alpha.Pc.p977 rfl rfl).trans ((runC_seq (m := 13) (m2 := 11) (j2 := 980) CFSG.KD.Fi24Alpha.Pc.p978 rfl rfl).trans ((runC_seq (m := 11) (m2 := 9) (j2 := 982) CFSG.KD.Fi24Alpha.Pc.p980 rfl rfl).trans ((runC_seq (m := 9) (m2 := 7) (j2 := 984) CFSG.KD.Fi24Alpha.Pc.p982 rfl rfl).trans ((runC_seq (m := 7) (m2 := 5) (j2 := 986) CFSG.KD.Fi24Alpha.Pc.p984 rfl rfl).trans ((runC_seq (m := 5) (m2 := 3) (j2 := 988) CFSG.KD.Fi24Alpha.Pc.p986 rfl rfl).trans (runC_seq (m := 3) (m2 := 1) (j2 := 990) CFSG.KD.Fi24Alpha.Pc.p988 rfl rfl)))))))))).trans CFSG.KD.Fi24Alpha.Pc.f69

end
