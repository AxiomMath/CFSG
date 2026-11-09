module

public import Certificates.Kernel.Sporadic.Fi24Cp.Data
public import CFSG.Certificates.Kernel.Ssa3Split
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

#kc_repo #kc_ktree CFSG.KD.Fi24Cp KV6 "Certificates/Kernel/Sporadic/Fi24Cp/data/v6.bin" 152491 4 22873650 818869021399491311

public section

open CFSG.KD.Fi24Cp CFSG.KC.Ssa3 CFSG.KC.Ssa3Split

@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v795 : Nat := CFSG.KD.Fi24Cp.KV6 0
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v796 : Nat := CFSG.KD.Fi24Cp.KV6 1
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l797 : List Nat := [CFSG.KD.Fi24Cp.Pc.v795, CFSG.KD.Fi24Cp.Pc.v796]
theorem CFSG.KD.Fi24Cp.Pc.p795 : Nat.beq (runC AR SD 795 (ckL CFSG.KD.Fi24Cp.Pc.l797) 2 795 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v797 : Nat := CFSG.KD.Fi24Cp.KV6 2
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v798 : Nat := CFSG.KD.Fi24Cp.KV6 3
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l799 : List Nat := [CFSG.KD.Fi24Cp.Pc.v795, CFSG.KD.Fi24Cp.Pc.v796, CFSG.KD.Fi24Cp.Pc.v797, CFSG.KD.Fi24Cp.Pc.v798]
theorem CFSG.KD.Fi24Cp.Pc.p797 : Nat.beq (runC AR SD 795 (ckL CFSG.KD.Fi24Cp.Pc.l799) 2 797 CFSG.KD.Fi24Cp.Pc.l797) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v799 : Nat := CFSG.KD.Fi24Cp.KV6 4
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v800 : Nat := CFSG.KD.Fi24Cp.KV6 5
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l801 : List Nat := [CFSG.KD.Fi24Cp.Pc.v795, CFSG.KD.Fi24Cp.Pc.v796, CFSG.KD.Fi24Cp.Pc.v797, CFSG.KD.Fi24Cp.Pc.v798, CFSG.KD.Fi24Cp.Pc.v799, CFSG.KD.Fi24Cp.Pc.v800]
theorem CFSG.KD.Fi24Cp.Pc.p799 : Nat.beq (runC AR SD 795 (ckL CFSG.KD.Fi24Cp.Pc.l801) 2 799 CFSG.KD.Fi24Cp.Pc.l799) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v801 : Nat := CFSG.KD.Fi24Cp.KV6 6
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v802 : Nat := CFSG.KD.Fi24Cp.KV6 7
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l803 : List Nat := [CFSG.KD.Fi24Cp.Pc.v795, CFSG.KD.Fi24Cp.Pc.v796, CFSG.KD.Fi24Cp.Pc.v797, CFSG.KD.Fi24Cp.Pc.v798, CFSG.KD.Fi24Cp.Pc.v799, CFSG.KD.Fi24Cp.Pc.v800, CFSG.KD.Fi24Cp.Pc.v801, CFSG.KD.Fi24Cp.Pc.v802]
theorem CFSG.KD.Fi24Cp.Pc.p801 : Nat.beq (runC AR SD 795 (ckL CFSG.KD.Fi24Cp.Pc.l803) 2 801 CFSG.KD.Fi24Cp.Pc.l801) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v803 : Nat := CFSG.KD.Fi24Cp.KV6 8
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v804 : Nat := CFSG.KD.Fi24Cp.KV6 9
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l805 : List Nat := [CFSG.KD.Fi24Cp.Pc.v795, CFSG.KD.Fi24Cp.Pc.v796, CFSG.KD.Fi24Cp.Pc.v797, CFSG.KD.Fi24Cp.Pc.v798, CFSG.KD.Fi24Cp.Pc.v799, CFSG.KD.Fi24Cp.Pc.v800, CFSG.KD.Fi24Cp.Pc.v801, CFSG.KD.Fi24Cp.Pc.v802, CFSG.KD.Fi24Cp.Pc.v803, CFSG.KD.Fi24Cp.Pc.v804]
theorem CFSG.KD.Fi24Cp.Pc.p803 : Nat.beq (runC AR SD 795 (ckL CFSG.KD.Fi24Cp.Pc.l805) 2 803 CFSG.KD.Fi24Cp.Pc.l803) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v805 : Nat := CFSG.KD.Fi24Cp.KV6 10
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v806 : Nat := CFSG.KD.Fi24Cp.KV6 11
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l807 : List Nat := [CFSG.KD.Fi24Cp.Pc.v795, CFSG.KD.Fi24Cp.Pc.v796, CFSG.KD.Fi24Cp.Pc.v797, CFSG.KD.Fi24Cp.Pc.v798, CFSG.KD.Fi24Cp.Pc.v799, CFSG.KD.Fi24Cp.Pc.v800, CFSG.KD.Fi24Cp.Pc.v801, CFSG.KD.Fi24Cp.Pc.v802, CFSG.KD.Fi24Cp.Pc.v803, CFSG.KD.Fi24Cp.Pc.v804, CFSG.KD.Fi24Cp.Pc.v805, CFSG.KD.Fi24Cp.Pc.v806]
theorem CFSG.KD.Fi24Cp.Pc.p805 : Nat.beq (runC AR SD 795 (ckL CFSG.KD.Fi24Cp.Pc.l807) 2 805 CFSG.KD.Fi24Cp.Pc.l805) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v807 : Nat := CFSG.KD.Fi24Cp.KV6 12
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v808 : Nat := CFSG.KD.Fi24Cp.KV6 13
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l809 : List Nat := [CFSG.KD.Fi24Cp.Pc.v795, CFSG.KD.Fi24Cp.Pc.v796, CFSG.KD.Fi24Cp.Pc.v797, CFSG.KD.Fi24Cp.Pc.v798, CFSG.KD.Fi24Cp.Pc.v799, CFSG.KD.Fi24Cp.Pc.v800, CFSG.KD.Fi24Cp.Pc.v801, CFSG.KD.Fi24Cp.Pc.v802, CFSG.KD.Fi24Cp.Pc.v803, CFSG.KD.Fi24Cp.Pc.v804, CFSG.KD.Fi24Cp.Pc.v805, CFSG.KD.Fi24Cp.Pc.v806, CFSG.KD.Fi24Cp.Pc.v807, CFSG.KD.Fi24Cp.Pc.v808]
theorem CFSG.KD.Fi24Cp.Pc.p807 : Nat.beq (runC AR SD 795 (ckL CFSG.KD.Fi24Cp.Pc.l809) 2 807 CFSG.KD.Fi24Cp.Pc.l807) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v809 : Nat := CFSG.KD.Fi24Cp.KV6 14
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v810 : Nat := CFSG.KD.Fi24Cp.KV6 15
theorem CFSG.KD.Fi24Cp.Pc.f60 : Nat.beq (runC AR SD 795 (finC AR SD (nat_lit 60) 795 811) 2 809 CFSG.KD.Fi24Cp.Pc.l809) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Cp.chk60 : chk (nat_lit 60) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 60) (lo := 795) (hi := 811) (m := 16) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 16) (m2 := 14) (j2 := 797) CFSG.KD.Fi24Cp.Pc.p795 rfl rfl).trans ((runC_seq (m := 14) (m2 := 12) (j2 := 799) CFSG.KD.Fi24Cp.Pc.p797 rfl rfl).trans ((runC_seq (m := 12) (m2 := 10) (j2 := 801) CFSG.KD.Fi24Cp.Pc.p799 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 803) CFSG.KD.Fi24Cp.Pc.p801 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 805) CFSG.KD.Fi24Cp.Pc.p803 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 807) CFSG.KD.Fi24Cp.Pc.p805 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 809) CFSG.KD.Fi24Cp.Pc.p807 rfl rfl))))))))).trans CFSG.KD.Fi24Cp.Pc.f60

@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v811 : Nat := CFSG.KD.Fi24Cp.KV6 16
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v812 : Nat := CFSG.KD.Fi24Cp.KV6 17
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l813 : List Nat := [CFSG.KD.Fi24Cp.Pc.v811, CFSG.KD.Fi24Cp.Pc.v812]
theorem CFSG.KD.Fi24Cp.Pc.p811 : Nat.beq (runC AR SD 811 (ckL CFSG.KD.Fi24Cp.Pc.l813) 2 811 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v813 : Nat := CFSG.KD.Fi24Cp.KV6 18
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v814 : Nat := CFSG.KD.Fi24Cp.KV6 19
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l815 : List Nat := [CFSG.KD.Fi24Cp.Pc.v811, CFSG.KD.Fi24Cp.Pc.v812, CFSG.KD.Fi24Cp.Pc.v813, CFSG.KD.Fi24Cp.Pc.v814]
theorem CFSG.KD.Fi24Cp.Pc.p813 : Nat.beq (runC AR SD 811 (ckL CFSG.KD.Fi24Cp.Pc.l815) 2 813 CFSG.KD.Fi24Cp.Pc.l813) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v815 : Nat := CFSG.KD.Fi24Cp.KV6 20
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v816 : Nat := CFSG.KD.Fi24Cp.KV6 21
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l817 : List Nat := [CFSG.KD.Fi24Cp.Pc.v811, CFSG.KD.Fi24Cp.Pc.v812, CFSG.KD.Fi24Cp.Pc.v813, CFSG.KD.Fi24Cp.Pc.v814, CFSG.KD.Fi24Cp.Pc.v815, CFSG.KD.Fi24Cp.Pc.v816]
theorem CFSG.KD.Fi24Cp.Pc.p815 : Nat.beq (runC AR SD 811 (ckL CFSG.KD.Fi24Cp.Pc.l817) 2 815 CFSG.KD.Fi24Cp.Pc.l815) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v817 : Nat := CFSG.KD.Fi24Cp.KV6 22
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l818 : List Nat := [CFSG.KD.Fi24Cp.Pc.v811, CFSG.KD.Fi24Cp.Pc.v812, CFSG.KD.Fi24Cp.Pc.v813, CFSG.KD.Fi24Cp.Pc.v814, CFSG.KD.Fi24Cp.Pc.v815, CFSG.KD.Fi24Cp.Pc.v816, CFSG.KD.Fi24Cp.Pc.v817]
theorem CFSG.KD.Fi24Cp.Pc.p817 : Nat.beq (runC AR SD 811 (ckL CFSG.KD.Fi24Cp.Pc.l818) 1 817 CFSG.KD.Fi24Cp.Pc.l817) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v818 : Nat := CFSG.KD.Fi24Cp.KV6 23
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v819 : Nat := CFSG.KD.Fi24Cp.KV6 24
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l820 : List Nat := [CFSG.KD.Fi24Cp.Pc.v811, CFSG.KD.Fi24Cp.Pc.v812, CFSG.KD.Fi24Cp.Pc.v813, CFSG.KD.Fi24Cp.Pc.v814, CFSG.KD.Fi24Cp.Pc.v815, CFSG.KD.Fi24Cp.Pc.v816, CFSG.KD.Fi24Cp.Pc.v817, CFSG.KD.Fi24Cp.Pc.v818, CFSG.KD.Fi24Cp.Pc.v819]
theorem CFSG.KD.Fi24Cp.Pc.p818 : Nat.beq (runC AR SD 811 (ckL CFSG.KD.Fi24Cp.Pc.l820) 2 818 CFSG.KD.Fi24Cp.Pc.l818) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v820 : Nat := CFSG.KD.Fi24Cp.KV6 25
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v821 : Nat := CFSG.KD.Fi24Cp.KV6 26
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l822 : List Nat := [CFSG.KD.Fi24Cp.Pc.v811, CFSG.KD.Fi24Cp.Pc.v812, CFSG.KD.Fi24Cp.Pc.v813, CFSG.KD.Fi24Cp.Pc.v814, CFSG.KD.Fi24Cp.Pc.v815, CFSG.KD.Fi24Cp.Pc.v816, CFSG.KD.Fi24Cp.Pc.v817, CFSG.KD.Fi24Cp.Pc.v818, CFSG.KD.Fi24Cp.Pc.v819, CFSG.KD.Fi24Cp.Pc.v820, CFSG.KD.Fi24Cp.Pc.v821]
theorem CFSG.KD.Fi24Cp.Pc.p820 : Nat.beq (runC AR SD 811 (ckL CFSG.KD.Fi24Cp.Pc.l822) 2 820 CFSG.KD.Fi24Cp.Pc.l820) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v822 : Nat := CFSG.KD.Fi24Cp.KV6 27
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v823 : Nat := CFSG.KD.Fi24Cp.KV6 28
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l824 : List Nat := [CFSG.KD.Fi24Cp.Pc.v811, CFSG.KD.Fi24Cp.Pc.v812, CFSG.KD.Fi24Cp.Pc.v813, CFSG.KD.Fi24Cp.Pc.v814, CFSG.KD.Fi24Cp.Pc.v815, CFSG.KD.Fi24Cp.Pc.v816, CFSG.KD.Fi24Cp.Pc.v817, CFSG.KD.Fi24Cp.Pc.v818, CFSG.KD.Fi24Cp.Pc.v819, CFSG.KD.Fi24Cp.Pc.v820, CFSG.KD.Fi24Cp.Pc.v821, CFSG.KD.Fi24Cp.Pc.v822, CFSG.KD.Fi24Cp.Pc.v823]
theorem CFSG.KD.Fi24Cp.Pc.p822 : Nat.beq (runC AR SD 811 (ckL CFSG.KD.Fi24Cp.Pc.l824) 2 822 CFSG.KD.Fi24Cp.Pc.l822) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v824 : Nat := CFSG.KD.Fi24Cp.KV6 29
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v825 : Nat := CFSG.KD.Fi24Cp.KV6 30
theorem CFSG.KD.Fi24Cp.Pc.f61 : Nat.beq (runC AR SD 811 (finC AR SD (nat_lit 61) 811 826) 2 824 CFSG.KD.Fi24Cp.Pc.l824) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Cp.chk61 : chk (nat_lit 61) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 61) (lo := 811) (hi := 826) (m := 15) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 15) (m2 := 13) (j2 := 813) CFSG.KD.Fi24Cp.Pc.p811 rfl rfl).trans ((runC_seq (m := 13) (m2 := 11) (j2 := 815) CFSG.KD.Fi24Cp.Pc.p813 rfl rfl).trans ((runC_seq (m := 11) (m2 := 9) (j2 := 817) CFSG.KD.Fi24Cp.Pc.p815 rfl rfl).trans ((runC_seq (m := 9) (m2 := 8) (j2 := 818) CFSG.KD.Fi24Cp.Pc.p817 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 820) CFSG.KD.Fi24Cp.Pc.p818 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 822) CFSG.KD.Fi24Cp.Pc.p820 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 824) CFSG.KD.Fi24Cp.Pc.p822 rfl rfl))))))))).trans CFSG.KD.Fi24Cp.Pc.f61

@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v826 : Nat := CFSG.KD.Fi24Cp.KV6 31
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v827 : Nat := CFSG.KD.Fi24Cp.KV6 32
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l828 : List Nat := [CFSG.KD.Fi24Cp.Pc.v826, CFSG.KD.Fi24Cp.Pc.v827]
theorem CFSG.KD.Fi24Cp.Pc.p826 : Nat.beq (runC AR SD 826 (ckL CFSG.KD.Fi24Cp.Pc.l828) 2 826 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v828 : Nat := CFSG.KD.Fi24Cp.KV6 33
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v829 : Nat := CFSG.KD.Fi24Cp.KV6 34
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l830 : List Nat := [CFSG.KD.Fi24Cp.Pc.v826, CFSG.KD.Fi24Cp.Pc.v827, CFSG.KD.Fi24Cp.Pc.v828, CFSG.KD.Fi24Cp.Pc.v829]
theorem CFSG.KD.Fi24Cp.Pc.p828 : Nat.beq (runC AR SD 826 (ckL CFSG.KD.Fi24Cp.Pc.l830) 2 828 CFSG.KD.Fi24Cp.Pc.l828) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v830 : Nat := CFSG.KD.Fi24Cp.KV6 35
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v831 : Nat := CFSG.KD.Fi24Cp.KV6 36
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l832 : List Nat := [CFSG.KD.Fi24Cp.Pc.v826, CFSG.KD.Fi24Cp.Pc.v827, CFSG.KD.Fi24Cp.Pc.v828, CFSG.KD.Fi24Cp.Pc.v829, CFSG.KD.Fi24Cp.Pc.v830, CFSG.KD.Fi24Cp.Pc.v831]
theorem CFSG.KD.Fi24Cp.Pc.p830 : Nat.beq (runC AR SD 826 (ckL CFSG.KD.Fi24Cp.Pc.l832) 2 830 CFSG.KD.Fi24Cp.Pc.l830) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v832 : Nat := CFSG.KD.Fi24Cp.KV6 37
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v833 : Nat := CFSG.KD.Fi24Cp.KV6 38
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l834 : List Nat := [CFSG.KD.Fi24Cp.Pc.v826, CFSG.KD.Fi24Cp.Pc.v827, CFSG.KD.Fi24Cp.Pc.v828, CFSG.KD.Fi24Cp.Pc.v829, CFSG.KD.Fi24Cp.Pc.v830, CFSG.KD.Fi24Cp.Pc.v831, CFSG.KD.Fi24Cp.Pc.v832, CFSG.KD.Fi24Cp.Pc.v833]
theorem CFSG.KD.Fi24Cp.Pc.p832 : Nat.beq (runC AR SD 826 (ckL CFSG.KD.Fi24Cp.Pc.l834) 2 832 CFSG.KD.Fi24Cp.Pc.l832) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v834 : Nat := CFSG.KD.Fi24Cp.KV6 39
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v835 : Nat := CFSG.KD.Fi24Cp.KV6 40
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l836 : List Nat := [CFSG.KD.Fi24Cp.Pc.v826, CFSG.KD.Fi24Cp.Pc.v827, CFSG.KD.Fi24Cp.Pc.v828, CFSG.KD.Fi24Cp.Pc.v829, CFSG.KD.Fi24Cp.Pc.v830, CFSG.KD.Fi24Cp.Pc.v831, CFSG.KD.Fi24Cp.Pc.v832, CFSG.KD.Fi24Cp.Pc.v833, CFSG.KD.Fi24Cp.Pc.v834, CFSG.KD.Fi24Cp.Pc.v835]
theorem CFSG.KD.Fi24Cp.Pc.p834 : Nat.beq (runC AR SD 826 (ckL CFSG.KD.Fi24Cp.Pc.l836) 2 834 CFSG.KD.Fi24Cp.Pc.l834) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v836 : Nat := CFSG.KD.Fi24Cp.KV6 41
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v837 : Nat := CFSG.KD.Fi24Cp.KV6 42
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l838 : List Nat := [CFSG.KD.Fi24Cp.Pc.v826, CFSG.KD.Fi24Cp.Pc.v827, CFSG.KD.Fi24Cp.Pc.v828, CFSG.KD.Fi24Cp.Pc.v829, CFSG.KD.Fi24Cp.Pc.v830, CFSG.KD.Fi24Cp.Pc.v831, CFSG.KD.Fi24Cp.Pc.v832, CFSG.KD.Fi24Cp.Pc.v833, CFSG.KD.Fi24Cp.Pc.v834, CFSG.KD.Fi24Cp.Pc.v835, CFSG.KD.Fi24Cp.Pc.v836, CFSG.KD.Fi24Cp.Pc.v837]
theorem CFSG.KD.Fi24Cp.Pc.p836 : Nat.beq (runC AR SD 826 (ckL CFSG.KD.Fi24Cp.Pc.l838) 2 836 CFSG.KD.Fi24Cp.Pc.l836) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v838 : Nat := CFSG.KD.Fi24Cp.KV6 43
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v839 : Nat := CFSG.KD.Fi24Cp.KV6 44
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l840 : List Nat := [CFSG.KD.Fi24Cp.Pc.v826, CFSG.KD.Fi24Cp.Pc.v827, CFSG.KD.Fi24Cp.Pc.v828, CFSG.KD.Fi24Cp.Pc.v829, CFSG.KD.Fi24Cp.Pc.v830, CFSG.KD.Fi24Cp.Pc.v831, CFSG.KD.Fi24Cp.Pc.v832, CFSG.KD.Fi24Cp.Pc.v833, CFSG.KD.Fi24Cp.Pc.v834, CFSG.KD.Fi24Cp.Pc.v835, CFSG.KD.Fi24Cp.Pc.v836, CFSG.KD.Fi24Cp.Pc.v837, CFSG.KD.Fi24Cp.Pc.v838, CFSG.KD.Fi24Cp.Pc.v839]
theorem CFSG.KD.Fi24Cp.Pc.p838 : Nat.beq (runC AR SD 826 (ckL CFSG.KD.Fi24Cp.Pc.l840) 2 838 CFSG.KD.Fi24Cp.Pc.l838) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v840 : Nat := CFSG.KD.Fi24Cp.KV6 45
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v841 : Nat := CFSG.KD.Fi24Cp.KV6 46
theorem CFSG.KD.Fi24Cp.Pc.f62 : Nat.beq (runC AR SD 826 (finC AR SD (nat_lit 62) 826 842) 2 840 CFSG.KD.Fi24Cp.Pc.l840) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Cp.chk62 : chk (nat_lit 62) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 62) (lo := 826) (hi := 842) (m := 16) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 16) (m2 := 14) (j2 := 828) CFSG.KD.Fi24Cp.Pc.p826 rfl rfl).trans ((runC_seq (m := 14) (m2 := 12) (j2 := 830) CFSG.KD.Fi24Cp.Pc.p828 rfl rfl).trans ((runC_seq (m := 12) (m2 := 10) (j2 := 832) CFSG.KD.Fi24Cp.Pc.p830 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 834) CFSG.KD.Fi24Cp.Pc.p832 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 836) CFSG.KD.Fi24Cp.Pc.p834 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 838) CFSG.KD.Fi24Cp.Pc.p836 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 840) CFSG.KD.Fi24Cp.Pc.p838 rfl rfl))))))))).trans CFSG.KD.Fi24Cp.Pc.f62

@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v842 : Nat := CFSG.KD.Fi24Cp.KV6 47
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v843 : Nat := CFSG.KD.Fi24Cp.KV6 48
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l844 : List Nat := [CFSG.KD.Fi24Cp.Pc.v842, CFSG.KD.Fi24Cp.Pc.v843]
theorem CFSG.KD.Fi24Cp.Pc.p842 : Nat.beq (runC AR SD 842 (ckL CFSG.KD.Fi24Cp.Pc.l844) 2 842 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v844 : Nat := CFSG.KD.Fi24Cp.KV6 49
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v845 : Nat := CFSG.KD.Fi24Cp.KV6 50
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l846 : List Nat := [CFSG.KD.Fi24Cp.Pc.v842, CFSG.KD.Fi24Cp.Pc.v843, CFSG.KD.Fi24Cp.Pc.v844, CFSG.KD.Fi24Cp.Pc.v845]
theorem CFSG.KD.Fi24Cp.Pc.p844 : Nat.beq (runC AR SD 842 (ckL CFSG.KD.Fi24Cp.Pc.l846) 2 844 CFSG.KD.Fi24Cp.Pc.l844) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v846 : Nat := CFSG.KD.Fi24Cp.KV6 51
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v847 : Nat := CFSG.KD.Fi24Cp.KV6 52
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l848 : List Nat := [CFSG.KD.Fi24Cp.Pc.v842, CFSG.KD.Fi24Cp.Pc.v843, CFSG.KD.Fi24Cp.Pc.v844, CFSG.KD.Fi24Cp.Pc.v845, CFSG.KD.Fi24Cp.Pc.v846, CFSG.KD.Fi24Cp.Pc.v847]
theorem CFSG.KD.Fi24Cp.Pc.p846 : Nat.beq (runC AR SD 842 (ckL CFSG.KD.Fi24Cp.Pc.l848) 2 846 CFSG.KD.Fi24Cp.Pc.l846) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v848 : Nat := CFSG.KD.Fi24Cp.KV6 53
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v849 : Nat := CFSG.KD.Fi24Cp.KV6 54
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l850 : List Nat := [CFSG.KD.Fi24Cp.Pc.v842, CFSG.KD.Fi24Cp.Pc.v843, CFSG.KD.Fi24Cp.Pc.v844, CFSG.KD.Fi24Cp.Pc.v845, CFSG.KD.Fi24Cp.Pc.v846, CFSG.KD.Fi24Cp.Pc.v847, CFSG.KD.Fi24Cp.Pc.v848, CFSG.KD.Fi24Cp.Pc.v849]
theorem CFSG.KD.Fi24Cp.Pc.p848 : Nat.beq (runC AR SD 842 (ckL CFSG.KD.Fi24Cp.Pc.l850) 2 848 CFSG.KD.Fi24Cp.Pc.l848) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v850 : Nat := CFSG.KD.Fi24Cp.KV6 55
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v851 : Nat := CFSG.KD.Fi24Cp.KV6 56
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l852 : List Nat := [CFSG.KD.Fi24Cp.Pc.v842, CFSG.KD.Fi24Cp.Pc.v843, CFSG.KD.Fi24Cp.Pc.v844, CFSG.KD.Fi24Cp.Pc.v845, CFSG.KD.Fi24Cp.Pc.v846, CFSG.KD.Fi24Cp.Pc.v847, CFSG.KD.Fi24Cp.Pc.v848, CFSG.KD.Fi24Cp.Pc.v849, CFSG.KD.Fi24Cp.Pc.v850, CFSG.KD.Fi24Cp.Pc.v851]
theorem CFSG.KD.Fi24Cp.Pc.p850 : Nat.beq (runC AR SD 842 (ckL CFSG.KD.Fi24Cp.Pc.l852) 2 850 CFSG.KD.Fi24Cp.Pc.l850) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v852 : Nat := CFSG.KD.Fi24Cp.KV6 57
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v853 : Nat := CFSG.KD.Fi24Cp.KV6 58
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l854 : List Nat := [CFSG.KD.Fi24Cp.Pc.v842, CFSG.KD.Fi24Cp.Pc.v843, CFSG.KD.Fi24Cp.Pc.v844, CFSG.KD.Fi24Cp.Pc.v845, CFSG.KD.Fi24Cp.Pc.v846, CFSG.KD.Fi24Cp.Pc.v847, CFSG.KD.Fi24Cp.Pc.v848, CFSG.KD.Fi24Cp.Pc.v849, CFSG.KD.Fi24Cp.Pc.v850, CFSG.KD.Fi24Cp.Pc.v851, CFSG.KD.Fi24Cp.Pc.v852, CFSG.KD.Fi24Cp.Pc.v853]
theorem CFSG.KD.Fi24Cp.Pc.p852 : Nat.beq (runC AR SD 842 (ckL CFSG.KD.Fi24Cp.Pc.l854) 2 852 CFSG.KD.Fi24Cp.Pc.l852) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v854 : Nat := CFSG.KD.Fi24Cp.KV6 59
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v855 : Nat := CFSG.KD.Fi24Cp.KV6 60
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l856 : List Nat := [CFSG.KD.Fi24Cp.Pc.v842, CFSG.KD.Fi24Cp.Pc.v843, CFSG.KD.Fi24Cp.Pc.v844, CFSG.KD.Fi24Cp.Pc.v845, CFSG.KD.Fi24Cp.Pc.v846, CFSG.KD.Fi24Cp.Pc.v847, CFSG.KD.Fi24Cp.Pc.v848, CFSG.KD.Fi24Cp.Pc.v849, CFSG.KD.Fi24Cp.Pc.v850, CFSG.KD.Fi24Cp.Pc.v851, CFSG.KD.Fi24Cp.Pc.v852, CFSG.KD.Fi24Cp.Pc.v853, CFSG.KD.Fi24Cp.Pc.v854, CFSG.KD.Fi24Cp.Pc.v855]
theorem CFSG.KD.Fi24Cp.Pc.p854 : Nat.beq (runC AR SD 842 (ckL CFSG.KD.Fi24Cp.Pc.l856) 2 854 CFSG.KD.Fi24Cp.Pc.l854) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v856 : Nat := CFSG.KD.Fi24Cp.KV6 61
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v857 : Nat := CFSG.KD.Fi24Cp.KV6 62
theorem CFSG.KD.Fi24Cp.Pc.f63 : Nat.beq (runC AR SD 842 (finC AR SD (nat_lit 63) 842 858) 2 856 CFSG.KD.Fi24Cp.Pc.l856) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Cp.chk63 : chk (nat_lit 63) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 63) (lo := 842) (hi := 858) (m := 16) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 16) (m2 := 14) (j2 := 844) CFSG.KD.Fi24Cp.Pc.p842 rfl rfl).trans ((runC_seq (m := 14) (m2 := 12) (j2 := 846) CFSG.KD.Fi24Cp.Pc.p844 rfl rfl).trans ((runC_seq (m := 12) (m2 := 10) (j2 := 848) CFSG.KD.Fi24Cp.Pc.p846 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 850) CFSG.KD.Fi24Cp.Pc.p848 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 852) CFSG.KD.Fi24Cp.Pc.p850 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 854) CFSG.KD.Fi24Cp.Pc.p852 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 856) CFSG.KD.Fi24Cp.Pc.p854 rfl rfl))))))))).trans CFSG.KD.Fi24Cp.Pc.f63

@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v858 : Nat := CFSG.KD.Fi24Cp.KV6 63
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v859 : Nat := CFSG.KD.Fi24Cp.KV6 64
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l860 : List Nat := [CFSG.KD.Fi24Cp.Pc.v858, CFSG.KD.Fi24Cp.Pc.v859]
theorem CFSG.KD.Fi24Cp.Pc.p858 : Nat.beq (runC AR SD 858 (ckL CFSG.KD.Fi24Cp.Pc.l860) 2 858 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v860 : Nat := CFSG.KD.Fi24Cp.KV6 65
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v861 : Nat := CFSG.KD.Fi24Cp.KV6 66
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l862 : List Nat := [CFSG.KD.Fi24Cp.Pc.v858, CFSG.KD.Fi24Cp.Pc.v859, CFSG.KD.Fi24Cp.Pc.v860, CFSG.KD.Fi24Cp.Pc.v861]
theorem CFSG.KD.Fi24Cp.Pc.p860 : Nat.beq (runC AR SD 858 (ckL CFSG.KD.Fi24Cp.Pc.l862) 2 860 CFSG.KD.Fi24Cp.Pc.l860) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v862 : Nat := CFSG.KD.Fi24Cp.KV6 67
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v863 : Nat := CFSG.KD.Fi24Cp.KV6 68
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l864 : List Nat := [CFSG.KD.Fi24Cp.Pc.v858, CFSG.KD.Fi24Cp.Pc.v859, CFSG.KD.Fi24Cp.Pc.v860, CFSG.KD.Fi24Cp.Pc.v861, CFSG.KD.Fi24Cp.Pc.v862, CFSG.KD.Fi24Cp.Pc.v863]
theorem CFSG.KD.Fi24Cp.Pc.p862 : Nat.beq (runC AR SD 858 (ckL CFSG.KD.Fi24Cp.Pc.l864) 2 862 CFSG.KD.Fi24Cp.Pc.l862) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v864 : Nat := CFSG.KD.Fi24Cp.KV6 69
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v865 : Nat := CFSG.KD.Fi24Cp.KV6 70
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l866 : List Nat := [CFSG.KD.Fi24Cp.Pc.v858, CFSG.KD.Fi24Cp.Pc.v859, CFSG.KD.Fi24Cp.Pc.v860, CFSG.KD.Fi24Cp.Pc.v861, CFSG.KD.Fi24Cp.Pc.v862, CFSG.KD.Fi24Cp.Pc.v863, CFSG.KD.Fi24Cp.Pc.v864, CFSG.KD.Fi24Cp.Pc.v865]
theorem CFSG.KD.Fi24Cp.Pc.p864 : Nat.beq (runC AR SD 858 (ckL CFSG.KD.Fi24Cp.Pc.l866) 2 864 CFSG.KD.Fi24Cp.Pc.l864) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v866 : Nat := CFSG.KD.Fi24Cp.KV6 71
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v867 : Nat := CFSG.KD.Fi24Cp.KV6 72
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l868 : List Nat := [CFSG.KD.Fi24Cp.Pc.v858, CFSG.KD.Fi24Cp.Pc.v859, CFSG.KD.Fi24Cp.Pc.v860, CFSG.KD.Fi24Cp.Pc.v861, CFSG.KD.Fi24Cp.Pc.v862, CFSG.KD.Fi24Cp.Pc.v863, CFSG.KD.Fi24Cp.Pc.v864, CFSG.KD.Fi24Cp.Pc.v865, CFSG.KD.Fi24Cp.Pc.v866, CFSG.KD.Fi24Cp.Pc.v867]
theorem CFSG.KD.Fi24Cp.Pc.p866 : Nat.beq (runC AR SD 858 (ckL CFSG.KD.Fi24Cp.Pc.l868) 2 866 CFSG.KD.Fi24Cp.Pc.l866) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v868 : Nat := CFSG.KD.Fi24Cp.KV6 73
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v869 : Nat := CFSG.KD.Fi24Cp.KV6 74
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l870 : List Nat := [CFSG.KD.Fi24Cp.Pc.v858, CFSG.KD.Fi24Cp.Pc.v859, CFSG.KD.Fi24Cp.Pc.v860, CFSG.KD.Fi24Cp.Pc.v861, CFSG.KD.Fi24Cp.Pc.v862, CFSG.KD.Fi24Cp.Pc.v863, CFSG.KD.Fi24Cp.Pc.v864, CFSG.KD.Fi24Cp.Pc.v865, CFSG.KD.Fi24Cp.Pc.v866, CFSG.KD.Fi24Cp.Pc.v867, CFSG.KD.Fi24Cp.Pc.v868, CFSG.KD.Fi24Cp.Pc.v869]
theorem CFSG.KD.Fi24Cp.Pc.p868 : Nat.beq (runC AR SD 858 (ckL CFSG.KD.Fi24Cp.Pc.l870) 2 868 CFSG.KD.Fi24Cp.Pc.l868) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v870 : Nat := CFSG.KD.Fi24Cp.KV6 75
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v871 : Nat := CFSG.KD.Fi24Cp.KV6 76
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l872 : List Nat := [CFSG.KD.Fi24Cp.Pc.v858, CFSG.KD.Fi24Cp.Pc.v859, CFSG.KD.Fi24Cp.Pc.v860, CFSG.KD.Fi24Cp.Pc.v861, CFSG.KD.Fi24Cp.Pc.v862, CFSG.KD.Fi24Cp.Pc.v863, CFSG.KD.Fi24Cp.Pc.v864, CFSG.KD.Fi24Cp.Pc.v865, CFSG.KD.Fi24Cp.Pc.v866, CFSG.KD.Fi24Cp.Pc.v867, CFSG.KD.Fi24Cp.Pc.v868, CFSG.KD.Fi24Cp.Pc.v869, CFSG.KD.Fi24Cp.Pc.v870, CFSG.KD.Fi24Cp.Pc.v871]
theorem CFSG.KD.Fi24Cp.Pc.p870 : Nat.beq (runC AR SD 858 (ckL CFSG.KD.Fi24Cp.Pc.l872) 2 870 CFSG.KD.Fi24Cp.Pc.l870) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v872 : Nat := CFSG.KD.Fi24Cp.KV6 77
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v873 : Nat := CFSG.KD.Fi24Cp.KV6 78
theorem CFSG.KD.Fi24Cp.Pc.f64 : Nat.beq (runC AR SD 858 (finC AR SD (nat_lit 64) 858 874) 2 872 CFSG.KD.Fi24Cp.Pc.l872) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Cp.chk64 : chk (nat_lit 64) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 64) (lo := 858) (hi := 874) (m := 16) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 16) (m2 := 14) (j2 := 860) CFSG.KD.Fi24Cp.Pc.p858 rfl rfl).trans ((runC_seq (m := 14) (m2 := 12) (j2 := 862) CFSG.KD.Fi24Cp.Pc.p860 rfl rfl).trans ((runC_seq (m := 12) (m2 := 10) (j2 := 864) CFSG.KD.Fi24Cp.Pc.p862 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 866) CFSG.KD.Fi24Cp.Pc.p864 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 868) CFSG.KD.Fi24Cp.Pc.p866 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 870) CFSG.KD.Fi24Cp.Pc.p868 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 872) CFSG.KD.Fi24Cp.Pc.p870 rfl rfl))))))))).trans CFSG.KD.Fi24Cp.Pc.f64

@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v874 : Nat := CFSG.KD.Fi24Cp.KV6 79
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v875 : Nat := CFSG.KD.Fi24Cp.KV6 80
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l876 : List Nat := [CFSG.KD.Fi24Cp.Pc.v874, CFSG.KD.Fi24Cp.Pc.v875]
theorem CFSG.KD.Fi24Cp.Pc.p874 : Nat.beq (runC AR SD 874 (ckL CFSG.KD.Fi24Cp.Pc.l876) 2 874 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v876 : Nat := CFSG.KD.Fi24Cp.KV6 81
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v877 : Nat := CFSG.KD.Fi24Cp.KV6 82
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l878 : List Nat := [CFSG.KD.Fi24Cp.Pc.v874, CFSG.KD.Fi24Cp.Pc.v875, CFSG.KD.Fi24Cp.Pc.v876, CFSG.KD.Fi24Cp.Pc.v877]
theorem CFSG.KD.Fi24Cp.Pc.p876 : Nat.beq (runC AR SD 874 (ckL CFSG.KD.Fi24Cp.Pc.l878) 2 876 CFSG.KD.Fi24Cp.Pc.l876) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v878 : Nat := CFSG.KD.Fi24Cp.KV6 83
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v879 : Nat := CFSG.KD.Fi24Cp.KV6 84
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l880 : List Nat := [CFSG.KD.Fi24Cp.Pc.v874, CFSG.KD.Fi24Cp.Pc.v875, CFSG.KD.Fi24Cp.Pc.v876, CFSG.KD.Fi24Cp.Pc.v877, CFSG.KD.Fi24Cp.Pc.v878, CFSG.KD.Fi24Cp.Pc.v879]
theorem CFSG.KD.Fi24Cp.Pc.p878 : Nat.beq (runC AR SD 874 (ckL CFSG.KD.Fi24Cp.Pc.l880) 2 878 CFSG.KD.Fi24Cp.Pc.l878) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v880 : Nat := CFSG.KD.Fi24Cp.KV6 85
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l881 : List Nat := [CFSG.KD.Fi24Cp.Pc.v874, CFSG.KD.Fi24Cp.Pc.v875, CFSG.KD.Fi24Cp.Pc.v876, CFSG.KD.Fi24Cp.Pc.v877, CFSG.KD.Fi24Cp.Pc.v878, CFSG.KD.Fi24Cp.Pc.v879, CFSG.KD.Fi24Cp.Pc.v880]
theorem CFSG.KD.Fi24Cp.Pc.p880 : Nat.beq (runC AR SD 874 (ckL CFSG.KD.Fi24Cp.Pc.l881) 1 880 CFSG.KD.Fi24Cp.Pc.l880) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v881 : Nat := CFSG.KD.Fi24Cp.KV6 86
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l882 : List Nat := [CFSG.KD.Fi24Cp.Pc.v874, CFSG.KD.Fi24Cp.Pc.v875, CFSG.KD.Fi24Cp.Pc.v876, CFSG.KD.Fi24Cp.Pc.v877, CFSG.KD.Fi24Cp.Pc.v878, CFSG.KD.Fi24Cp.Pc.v879, CFSG.KD.Fi24Cp.Pc.v880, CFSG.KD.Fi24Cp.Pc.v881]
theorem CFSG.KD.Fi24Cp.Pc.p881 : Nat.beq (runC AR SD 874 (ckL CFSG.KD.Fi24Cp.Pc.l882) 1 881 CFSG.KD.Fi24Cp.Pc.l881) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v882 : Nat := CFSG.KD.Fi24Cp.KV6 87
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l883 : List Nat := [CFSG.KD.Fi24Cp.Pc.v874, CFSG.KD.Fi24Cp.Pc.v875, CFSG.KD.Fi24Cp.Pc.v876, CFSG.KD.Fi24Cp.Pc.v877, CFSG.KD.Fi24Cp.Pc.v878, CFSG.KD.Fi24Cp.Pc.v879, CFSG.KD.Fi24Cp.Pc.v880, CFSG.KD.Fi24Cp.Pc.v881, CFSG.KD.Fi24Cp.Pc.v882]
theorem CFSG.KD.Fi24Cp.Pc.p882 : Nat.beq (runC AR SD 874 (ckL CFSG.KD.Fi24Cp.Pc.l883) 1 882 CFSG.KD.Fi24Cp.Pc.l882) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v883 : Nat := CFSG.KD.Fi24Cp.KV6 88
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v884 : Nat := CFSG.KD.Fi24Cp.KV6 89
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l885 : List Nat := [CFSG.KD.Fi24Cp.Pc.v874, CFSG.KD.Fi24Cp.Pc.v875, CFSG.KD.Fi24Cp.Pc.v876, CFSG.KD.Fi24Cp.Pc.v877, CFSG.KD.Fi24Cp.Pc.v878, CFSG.KD.Fi24Cp.Pc.v879, CFSG.KD.Fi24Cp.Pc.v880, CFSG.KD.Fi24Cp.Pc.v881, CFSG.KD.Fi24Cp.Pc.v882, CFSG.KD.Fi24Cp.Pc.v883, CFSG.KD.Fi24Cp.Pc.v884]
theorem CFSG.KD.Fi24Cp.Pc.p883 : Nat.beq (runC AR SD 874 (ckL CFSG.KD.Fi24Cp.Pc.l885) 2 883 CFSG.KD.Fi24Cp.Pc.l883) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v885 : Nat := CFSG.KD.Fi24Cp.KV6 90
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v886 : Nat := CFSG.KD.Fi24Cp.KV6 91
theorem CFSG.KD.Fi24Cp.Pc.f65 : Nat.beq (runC AR SD 874 (finC AR SD (nat_lit 65) 874 887) 2 885 CFSG.KD.Fi24Cp.Pc.l885) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Cp.chk65 : chk (nat_lit 65) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 65) (lo := 874) (hi := 887) (m := 13) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 13) (m2 := 11) (j2 := 876) CFSG.KD.Fi24Cp.Pc.p874 rfl rfl).trans ((runC_seq (m := 11) (m2 := 9) (j2 := 878) CFSG.KD.Fi24Cp.Pc.p876 rfl rfl).trans ((runC_seq (m := 9) (m2 := 7) (j2 := 880) CFSG.KD.Fi24Cp.Pc.p878 rfl rfl).trans ((runC_seq (m := 7) (m2 := 6) (j2 := 881) CFSG.KD.Fi24Cp.Pc.p880 rfl rfl).trans ((runC_seq (m := 6) (m2 := 5) (j2 := 882) CFSG.KD.Fi24Cp.Pc.p881 rfl rfl).trans ((runC_seq (m := 5) (m2 := 4) (j2 := 883) CFSG.KD.Fi24Cp.Pc.p882 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 885) CFSG.KD.Fi24Cp.Pc.p883 rfl rfl))))))))).trans CFSG.KD.Fi24Cp.Pc.f65

@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v887 : Nat := CFSG.KD.Fi24Cp.KV6 92
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v888 : Nat := CFSG.KD.Fi24Cp.KV6 93
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l889 : List Nat := [CFSG.KD.Fi24Cp.Pc.v887, CFSG.KD.Fi24Cp.Pc.v888]
theorem CFSG.KD.Fi24Cp.Pc.p887 : Nat.beq (runC AR SD 887 (ckL CFSG.KD.Fi24Cp.Pc.l889) 2 887 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v889 : Nat := CFSG.KD.Fi24Cp.KV6 94
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v890 : Nat := CFSG.KD.Fi24Cp.KV6 95
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l891 : List Nat := [CFSG.KD.Fi24Cp.Pc.v887, CFSG.KD.Fi24Cp.Pc.v888, CFSG.KD.Fi24Cp.Pc.v889, CFSG.KD.Fi24Cp.Pc.v890]
theorem CFSG.KD.Fi24Cp.Pc.p889 : Nat.beq (runC AR SD 887 (ckL CFSG.KD.Fi24Cp.Pc.l891) 2 889 CFSG.KD.Fi24Cp.Pc.l889) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v891 : Nat := CFSG.KD.Fi24Cp.KV6 96
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v892 : Nat := CFSG.KD.Fi24Cp.KV6 97
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l893 : List Nat := [CFSG.KD.Fi24Cp.Pc.v887, CFSG.KD.Fi24Cp.Pc.v888, CFSG.KD.Fi24Cp.Pc.v889, CFSG.KD.Fi24Cp.Pc.v890, CFSG.KD.Fi24Cp.Pc.v891, CFSG.KD.Fi24Cp.Pc.v892]
theorem CFSG.KD.Fi24Cp.Pc.p891 : Nat.beq (runC AR SD 887 (ckL CFSG.KD.Fi24Cp.Pc.l893) 2 891 CFSG.KD.Fi24Cp.Pc.l891) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v893 : Nat := CFSG.KD.Fi24Cp.KV6 98
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v894 : Nat := CFSG.KD.Fi24Cp.KV6 99
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l895 : List Nat := [CFSG.KD.Fi24Cp.Pc.v887, CFSG.KD.Fi24Cp.Pc.v888, CFSG.KD.Fi24Cp.Pc.v889, CFSG.KD.Fi24Cp.Pc.v890, CFSG.KD.Fi24Cp.Pc.v891, CFSG.KD.Fi24Cp.Pc.v892, CFSG.KD.Fi24Cp.Pc.v893, CFSG.KD.Fi24Cp.Pc.v894]
theorem CFSG.KD.Fi24Cp.Pc.p893 : Nat.beq (runC AR SD 887 (ckL CFSG.KD.Fi24Cp.Pc.l895) 2 893 CFSG.KD.Fi24Cp.Pc.l893) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v895 : Nat := CFSG.KD.Fi24Cp.KV6 100
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v896 : Nat := CFSG.KD.Fi24Cp.KV6 101
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l897 : List Nat := [CFSG.KD.Fi24Cp.Pc.v887, CFSG.KD.Fi24Cp.Pc.v888, CFSG.KD.Fi24Cp.Pc.v889, CFSG.KD.Fi24Cp.Pc.v890, CFSG.KD.Fi24Cp.Pc.v891, CFSG.KD.Fi24Cp.Pc.v892, CFSG.KD.Fi24Cp.Pc.v893, CFSG.KD.Fi24Cp.Pc.v894, CFSG.KD.Fi24Cp.Pc.v895, CFSG.KD.Fi24Cp.Pc.v896]
theorem CFSG.KD.Fi24Cp.Pc.p895 : Nat.beq (runC AR SD 887 (ckL CFSG.KD.Fi24Cp.Pc.l897) 2 895 CFSG.KD.Fi24Cp.Pc.l895) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v897 : Nat := CFSG.KD.Fi24Cp.KV6 102
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v898 : Nat := CFSG.KD.Fi24Cp.KV6 103
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l899 : List Nat := [CFSG.KD.Fi24Cp.Pc.v887, CFSG.KD.Fi24Cp.Pc.v888, CFSG.KD.Fi24Cp.Pc.v889, CFSG.KD.Fi24Cp.Pc.v890, CFSG.KD.Fi24Cp.Pc.v891, CFSG.KD.Fi24Cp.Pc.v892, CFSG.KD.Fi24Cp.Pc.v893, CFSG.KD.Fi24Cp.Pc.v894, CFSG.KD.Fi24Cp.Pc.v895, CFSG.KD.Fi24Cp.Pc.v896, CFSG.KD.Fi24Cp.Pc.v897, CFSG.KD.Fi24Cp.Pc.v898]
theorem CFSG.KD.Fi24Cp.Pc.p897 : Nat.beq (runC AR SD 887 (ckL CFSG.KD.Fi24Cp.Pc.l899) 2 897 CFSG.KD.Fi24Cp.Pc.l897) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v899 : Nat := CFSG.KD.Fi24Cp.KV6 104
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v900 : Nat := CFSG.KD.Fi24Cp.KV6 105
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l901 : List Nat := [CFSG.KD.Fi24Cp.Pc.v887, CFSG.KD.Fi24Cp.Pc.v888, CFSG.KD.Fi24Cp.Pc.v889, CFSG.KD.Fi24Cp.Pc.v890, CFSG.KD.Fi24Cp.Pc.v891, CFSG.KD.Fi24Cp.Pc.v892, CFSG.KD.Fi24Cp.Pc.v893, CFSG.KD.Fi24Cp.Pc.v894, CFSG.KD.Fi24Cp.Pc.v895, CFSG.KD.Fi24Cp.Pc.v896, CFSG.KD.Fi24Cp.Pc.v897, CFSG.KD.Fi24Cp.Pc.v898, CFSG.KD.Fi24Cp.Pc.v899, CFSG.KD.Fi24Cp.Pc.v900]
theorem CFSG.KD.Fi24Cp.Pc.p899 : Nat.beq (runC AR SD 887 (ckL CFSG.KD.Fi24Cp.Pc.l901) 2 899 CFSG.KD.Fi24Cp.Pc.l899) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v901 : Nat := CFSG.KD.Fi24Cp.KV6 106
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v902 : Nat := CFSG.KD.Fi24Cp.KV6 107
theorem CFSG.KD.Fi24Cp.Pc.f66 : Nat.beq (runC AR SD 887 (finC AR SD (nat_lit 66) 887 903) 2 901 CFSG.KD.Fi24Cp.Pc.l901) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Cp.chk66 : chk (nat_lit 66) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 66) (lo := 887) (hi := 903) (m := 16) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 16) (m2 := 14) (j2 := 889) CFSG.KD.Fi24Cp.Pc.p887 rfl rfl).trans ((runC_seq (m := 14) (m2 := 12) (j2 := 891) CFSG.KD.Fi24Cp.Pc.p889 rfl rfl).trans ((runC_seq (m := 12) (m2 := 10) (j2 := 893) CFSG.KD.Fi24Cp.Pc.p891 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 895) CFSG.KD.Fi24Cp.Pc.p893 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 897) CFSG.KD.Fi24Cp.Pc.p895 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 899) CFSG.KD.Fi24Cp.Pc.p897 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 901) CFSG.KD.Fi24Cp.Pc.p899 rfl rfl))))))))).trans CFSG.KD.Fi24Cp.Pc.f66

@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v903 : Nat := CFSG.KD.Fi24Cp.KV6 108
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v904 : Nat := CFSG.KD.Fi24Cp.KV6 109
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l905 : List Nat := [CFSG.KD.Fi24Cp.Pc.v903, CFSG.KD.Fi24Cp.Pc.v904]
theorem CFSG.KD.Fi24Cp.Pc.p903 : Nat.beq (runC AR SD 903 (ckL CFSG.KD.Fi24Cp.Pc.l905) 2 903 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v905 : Nat := CFSG.KD.Fi24Cp.KV6 110
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v906 : Nat := CFSG.KD.Fi24Cp.KV6 111
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l907 : List Nat := [CFSG.KD.Fi24Cp.Pc.v903, CFSG.KD.Fi24Cp.Pc.v904, CFSG.KD.Fi24Cp.Pc.v905, CFSG.KD.Fi24Cp.Pc.v906]
theorem CFSG.KD.Fi24Cp.Pc.p905 : Nat.beq (runC AR SD 903 (ckL CFSG.KD.Fi24Cp.Pc.l907) 2 905 CFSG.KD.Fi24Cp.Pc.l905) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v907 : Nat := CFSG.KD.Fi24Cp.KV6 112
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v908 : Nat := CFSG.KD.Fi24Cp.KV6 113
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l909 : List Nat := [CFSG.KD.Fi24Cp.Pc.v903, CFSG.KD.Fi24Cp.Pc.v904, CFSG.KD.Fi24Cp.Pc.v905, CFSG.KD.Fi24Cp.Pc.v906, CFSG.KD.Fi24Cp.Pc.v907, CFSG.KD.Fi24Cp.Pc.v908]
theorem CFSG.KD.Fi24Cp.Pc.p907 : Nat.beq (runC AR SD 903 (ckL CFSG.KD.Fi24Cp.Pc.l909) 2 907 CFSG.KD.Fi24Cp.Pc.l907) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v909 : Nat := CFSG.KD.Fi24Cp.KV6 114
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v910 : Nat := CFSG.KD.Fi24Cp.KV6 115
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l911 : List Nat := [CFSG.KD.Fi24Cp.Pc.v903, CFSG.KD.Fi24Cp.Pc.v904, CFSG.KD.Fi24Cp.Pc.v905, CFSG.KD.Fi24Cp.Pc.v906, CFSG.KD.Fi24Cp.Pc.v907, CFSG.KD.Fi24Cp.Pc.v908, CFSG.KD.Fi24Cp.Pc.v909, CFSG.KD.Fi24Cp.Pc.v910]
theorem CFSG.KD.Fi24Cp.Pc.p909 : Nat.beq (runC AR SD 903 (ckL CFSG.KD.Fi24Cp.Pc.l911) 2 909 CFSG.KD.Fi24Cp.Pc.l909) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v911 : Nat := CFSG.KD.Fi24Cp.KV6 116
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v912 : Nat := CFSG.KD.Fi24Cp.KV6 117
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l913 : List Nat := [CFSG.KD.Fi24Cp.Pc.v903, CFSG.KD.Fi24Cp.Pc.v904, CFSG.KD.Fi24Cp.Pc.v905, CFSG.KD.Fi24Cp.Pc.v906, CFSG.KD.Fi24Cp.Pc.v907, CFSG.KD.Fi24Cp.Pc.v908, CFSG.KD.Fi24Cp.Pc.v909, CFSG.KD.Fi24Cp.Pc.v910, CFSG.KD.Fi24Cp.Pc.v911, CFSG.KD.Fi24Cp.Pc.v912]
theorem CFSG.KD.Fi24Cp.Pc.p911 : Nat.beq (runC AR SD 903 (ckL CFSG.KD.Fi24Cp.Pc.l913) 2 911 CFSG.KD.Fi24Cp.Pc.l911) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v913 : Nat := CFSG.KD.Fi24Cp.KV6 118
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v914 : Nat := CFSG.KD.Fi24Cp.KV6 119
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l915 : List Nat := [CFSG.KD.Fi24Cp.Pc.v903, CFSG.KD.Fi24Cp.Pc.v904, CFSG.KD.Fi24Cp.Pc.v905, CFSG.KD.Fi24Cp.Pc.v906, CFSG.KD.Fi24Cp.Pc.v907, CFSG.KD.Fi24Cp.Pc.v908, CFSG.KD.Fi24Cp.Pc.v909, CFSG.KD.Fi24Cp.Pc.v910, CFSG.KD.Fi24Cp.Pc.v911, CFSG.KD.Fi24Cp.Pc.v912, CFSG.KD.Fi24Cp.Pc.v913, CFSG.KD.Fi24Cp.Pc.v914]
theorem CFSG.KD.Fi24Cp.Pc.p913 : Nat.beq (runC AR SD 903 (ckL CFSG.KD.Fi24Cp.Pc.l915) 2 913 CFSG.KD.Fi24Cp.Pc.l913) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v915 : Nat := CFSG.KD.Fi24Cp.KV6 120
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v916 : Nat := CFSG.KD.Fi24Cp.KV6 121
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l917 : List Nat := [CFSG.KD.Fi24Cp.Pc.v903, CFSG.KD.Fi24Cp.Pc.v904, CFSG.KD.Fi24Cp.Pc.v905, CFSG.KD.Fi24Cp.Pc.v906, CFSG.KD.Fi24Cp.Pc.v907, CFSG.KD.Fi24Cp.Pc.v908, CFSG.KD.Fi24Cp.Pc.v909, CFSG.KD.Fi24Cp.Pc.v910, CFSG.KD.Fi24Cp.Pc.v911, CFSG.KD.Fi24Cp.Pc.v912, CFSG.KD.Fi24Cp.Pc.v913, CFSG.KD.Fi24Cp.Pc.v914, CFSG.KD.Fi24Cp.Pc.v915, CFSG.KD.Fi24Cp.Pc.v916]
theorem CFSG.KD.Fi24Cp.Pc.p915 : Nat.beq (runC AR SD 903 (ckL CFSG.KD.Fi24Cp.Pc.l917) 2 915 CFSG.KD.Fi24Cp.Pc.l915) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v917 : Nat := CFSG.KD.Fi24Cp.KV6 122
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v918 : Nat := CFSG.KD.Fi24Cp.KV6 123
theorem CFSG.KD.Fi24Cp.Pc.f67 : Nat.beq (runC AR SD 903 (finC AR SD (nat_lit 67) 903 919) 2 917 CFSG.KD.Fi24Cp.Pc.l917) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Cp.chk67 : chk (nat_lit 67) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 67) (lo := 903) (hi := 919) (m := 16) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 16) (m2 := 14) (j2 := 905) CFSG.KD.Fi24Cp.Pc.p903 rfl rfl).trans ((runC_seq (m := 14) (m2 := 12) (j2 := 907) CFSG.KD.Fi24Cp.Pc.p905 rfl rfl).trans ((runC_seq (m := 12) (m2 := 10) (j2 := 909) CFSG.KD.Fi24Cp.Pc.p907 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 911) CFSG.KD.Fi24Cp.Pc.p909 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 913) CFSG.KD.Fi24Cp.Pc.p911 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 915) CFSG.KD.Fi24Cp.Pc.p913 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 917) CFSG.KD.Fi24Cp.Pc.p915 rfl rfl))))))))).trans CFSG.KD.Fi24Cp.Pc.f67

@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v919 : Nat := CFSG.KD.Fi24Cp.KV6 124
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v920 : Nat := CFSG.KD.Fi24Cp.KV6 125
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l921 : List Nat := [CFSG.KD.Fi24Cp.Pc.v919, CFSG.KD.Fi24Cp.Pc.v920]
theorem CFSG.KD.Fi24Cp.Pc.p919 : Nat.beq (runC AR SD 919 (ckL CFSG.KD.Fi24Cp.Pc.l921) 2 919 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v921 : Nat := CFSG.KD.Fi24Cp.KV6 126
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v922 : Nat := CFSG.KD.Fi24Cp.KV6 127
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l923 : List Nat := [CFSG.KD.Fi24Cp.Pc.v919, CFSG.KD.Fi24Cp.Pc.v920, CFSG.KD.Fi24Cp.Pc.v921, CFSG.KD.Fi24Cp.Pc.v922]
theorem CFSG.KD.Fi24Cp.Pc.p921 : Nat.beq (runC AR SD 919 (ckL CFSG.KD.Fi24Cp.Pc.l923) 2 921 CFSG.KD.Fi24Cp.Pc.l921) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v923 : Nat := CFSG.KD.Fi24Cp.KV6 128
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v924 : Nat := CFSG.KD.Fi24Cp.KV6 129
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l925 : List Nat := [CFSG.KD.Fi24Cp.Pc.v919, CFSG.KD.Fi24Cp.Pc.v920, CFSG.KD.Fi24Cp.Pc.v921, CFSG.KD.Fi24Cp.Pc.v922, CFSG.KD.Fi24Cp.Pc.v923, CFSG.KD.Fi24Cp.Pc.v924]
theorem CFSG.KD.Fi24Cp.Pc.p923 : Nat.beq (runC AR SD 919 (ckL CFSG.KD.Fi24Cp.Pc.l925) 2 923 CFSG.KD.Fi24Cp.Pc.l923) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a925_3 : Nat := CFSG.KD.Fi24Cp.KV6 130
theorem CFSG.KD.Fi24Cp.Pc.q925_3 : Nat.beq (powTop AR.mul (getV AR SD 919 CFSG.KD.Fi24Cp.Pc.l925 (SD.na.getD 925 0)) (SD.nk.getD 925 1) 3 (ckP CFSG.KD.Fi24Cp.Pc.a925_3) 13 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a925_2 : Nat := CFSG.KD.Fi24Cp.KV6 131
theorem CFSG.KD.Fi24Cp.Pc.q925_2 : Nat.beq (powTop AR.mul (getV AR SD 919 CFSG.KD.Fi24Cp.Pc.l925 (SD.na.getD 925 0)) (SD.nk.getD 925 1) 2 (ckP CFSG.KD.Fi24Cp.Pc.a925_2) 1 CFSG.KD.Fi24Cp.Pc.a925_3 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a925_1 : Nat := CFSG.KD.Fi24Cp.KV6 132
theorem CFSG.KD.Fi24Cp.Pc.q925_1 : Nat.beq (powTop AR.mul (getV AR SD 919 CFSG.KD.Fi24Cp.Pc.l925 (SD.na.getD 925 0)) (SD.nk.getD 925 1) 1 (ckP CFSG.KD.Fi24Cp.Pc.a925_1) 1 CFSG.KD.Fi24Cp.Pc.a925_2 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v925 : Nat := CFSG.KD.Fi24Cp.KV6 133
theorem CFSG.KD.Fi24Cp.Pc.r925 : Nat.beq (powR AR.mul AR.one (getV AR SD 919 CFSG.KD.Fi24Cp.Pc.l925 (SD.na.getD 925 0)) (SD.nk.getD 925 1) 1 CFSG.KD.Fi24Cp.Pc.a925_1 true) CFSG.KD.Fi24Cp.Pc.v925 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v926 : Nat := CFSG.KD.Fi24Cp.KV6 134
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v927 : Nat := CFSG.KD.Fi24Cp.KV6 135
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l926 : List Nat := [CFSG.KD.Fi24Cp.Pc.v919, CFSG.KD.Fi24Cp.Pc.v920, CFSG.KD.Fi24Cp.Pc.v921, CFSG.KD.Fi24Cp.Pc.v922, CFSG.KD.Fi24Cp.Pc.v923, CFSG.KD.Fi24Cp.Pc.v924, CFSG.KD.Fi24Cp.Pc.v925]
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l928 : List Nat := [CFSG.KD.Fi24Cp.Pc.v919, CFSG.KD.Fi24Cp.Pc.v920, CFSG.KD.Fi24Cp.Pc.v921, CFSG.KD.Fi24Cp.Pc.v922, CFSG.KD.Fi24Cp.Pc.v923, CFSG.KD.Fi24Cp.Pc.v924, CFSG.KD.Fi24Cp.Pc.v925, CFSG.KD.Fi24Cp.Pc.v926, CFSG.KD.Fi24Cp.Pc.v927]
theorem CFSG.KD.Fi24Cp.Pc.p926 : Nat.beq (runC AR SD 919 (ckL CFSG.KD.Fi24Cp.Pc.l928) 2 926 CFSG.KD.Fi24Cp.Pc.l926) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v928 : Nat := CFSG.KD.Fi24Cp.KV6 136
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v929 : Nat := CFSG.KD.Fi24Cp.KV6 137
theorem CFSG.KD.Fi24Cp.Pc.f68 : Nat.beq (runC AR SD 919 (finC AR SD (nat_lit 68) 919 930) 2 928 CFSG.KD.Fi24Cp.Pc.l928) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Cp.chk68 : chk (nat_lit 68) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 68) (lo := 919) (hi := 930) (m := 11) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 11) (m2 := 9) (j2 := 921) CFSG.KD.Fi24Cp.Pc.p919 rfl rfl).trans ((runC_seq (m := 9) (m2 := 7) (j2 := 923) CFSG.KD.Fi24Cp.Pc.p921 rfl rfl).trans ((runC_seq (m := 7) (m2 := 5) (j2 := 925) CFSG.KD.Fi24Cp.Pc.p923 rfl rfl).trans ((runC_node (m := 5) (m2 := 4) (j2 := 926) (Lr := CFSG.KD.Fi24Cp.Pc.l926) ((nodeV_pow (R := AR) (D := SD) (lo := 919) (L := CFSG.KD.Fi24Cp.Pc.l925) (j := 925) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 919 CFSG.KD.Fi24Cp.Pc.l925 (SD.na.getD 925 0)) (SD.nk.getD 925 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Cp.Pc.q925_3 rfl).trans ((powR_seq (n := 3) CFSG.KD.Fi24Cp.Pc.q925_2 rfl).trans ((powR_seq (n := 2) CFSG.KD.Fi24Cp.Pc.q925_1 rfl).trans (powR_last CFSG.KD.Fi24Cp.Pc.r925)))))) (by quickRfl) rfl rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 928) CFSG.KD.Fi24Cp.Pc.p926 rfl rfl))))))).trans CFSG.KD.Fi24Cp.Pc.f68

@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v930 : Nat := CFSG.KD.Fi24Cp.KV6 138
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v931 : Nat := CFSG.KD.Fi24Cp.KV6 139
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l932 : List Nat := [CFSG.KD.Fi24Cp.Pc.v930, CFSG.KD.Fi24Cp.Pc.v931]
theorem CFSG.KD.Fi24Cp.Pc.p930 : Nat.beq (runC AR SD 930 (ckL CFSG.KD.Fi24Cp.Pc.l932) 2 930 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a932_3 : Nat := CFSG.KD.Fi24Cp.KV6 140
theorem CFSG.KD.Fi24Cp.Pc.q932_3 : Nat.beq (powTop AR.mul (getV AR SD 930 CFSG.KD.Fi24Cp.Pc.l932 (SD.na.getD 932 0)) (SD.nk.getD 932 1) 3 (ckP CFSG.KD.Fi24Cp.Pc.a932_3) 13 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a932_2 : Nat := CFSG.KD.Fi24Cp.KV6 141
theorem CFSG.KD.Fi24Cp.Pc.q932_2 : Nat.beq (powTop AR.mul (getV AR SD 930 CFSG.KD.Fi24Cp.Pc.l932 (SD.na.getD 932 0)) (SD.nk.getD 932 1) 2 (ckP CFSG.KD.Fi24Cp.Pc.a932_2) 1 CFSG.KD.Fi24Cp.Pc.a932_3 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a932_1 : Nat := CFSG.KD.Fi24Cp.KV6 142
theorem CFSG.KD.Fi24Cp.Pc.q932_1 : Nat.beq (powTop AR.mul (getV AR SD 930 CFSG.KD.Fi24Cp.Pc.l932 (SD.na.getD 932 0)) (SD.nk.getD 932 1) 1 (ckP CFSG.KD.Fi24Cp.Pc.a932_1) 1 CFSG.KD.Fi24Cp.Pc.a932_2 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v932 : Nat := CFSG.KD.Fi24Cp.KV6 143
theorem CFSG.KD.Fi24Cp.Pc.r932 : Nat.beq (powR AR.mul AR.one (getV AR SD 930 CFSG.KD.Fi24Cp.Pc.l932 (SD.na.getD 932 0)) (SD.nk.getD 932 1) 1 CFSG.KD.Fi24Cp.Pc.a932_1 true) CFSG.KD.Fi24Cp.Pc.v932 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v933 : Nat := CFSG.KD.Fi24Cp.KV6 144
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v934 : Nat := CFSG.KD.Fi24Cp.KV6 145
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l933 : List Nat := [CFSG.KD.Fi24Cp.Pc.v930, CFSG.KD.Fi24Cp.Pc.v931, CFSG.KD.Fi24Cp.Pc.v932]
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l935 : List Nat := [CFSG.KD.Fi24Cp.Pc.v930, CFSG.KD.Fi24Cp.Pc.v931, CFSG.KD.Fi24Cp.Pc.v932, CFSG.KD.Fi24Cp.Pc.v933, CFSG.KD.Fi24Cp.Pc.v934]
theorem CFSG.KD.Fi24Cp.Pc.p933 : Nat.beq (runC AR SD 930 (ckL CFSG.KD.Fi24Cp.Pc.l935) 2 933 CFSG.KD.Fi24Cp.Pc.l933) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v935 : Nat := CFSG.KD.Fi24Cp.KV6 146
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v936 : Nat := CFSG.KD.Fi24Cp.KV6 147
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l937 : List Nat := [CFSG.KD.Fi24Cp.Pc.v930, CFSG.KD.Fi24Cp.Pc.v931, CFSG.KD.Fi24Cp.Pc.v932, CFSG.KD.Fi24Cp.Pc.v933, CFSG.KD.Fi24Cp.Pc.v934, CFSG.KD.Fi24Cp.Pc.v935, CFSG.KD.Fi24Cp.Pc.v936]
theorem CFSG.KD.Fi24Cp.Pc.p935 : Nat.beq (runC AR SD 930 (ckL CFSG.KD.Fi24Cp.Pc.l937) 2 935 CFSG.KD.Fi24Cp.Pc.l935) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v937 : Nat := CFSG.KD.Fi24Cp.KV6 148
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v938 : Nat := CFSG.KD.Fi24Cp.KV6 149
theorem CFSG.KD.Fi24Cp.Pc.f69 : Nat.beq (runC AR SD 930 (finC AR SD (nat_lit 69) 930 939) 2 937 CFSG.KD.Fi24Cp.Pc.l937) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Cp.chk69 : chk (nat_lit 69) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 69) (lo := 930) (hi := 939) (m := 9) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 9) (m2 := 7) (j2 := 932) CFSG.KD.Fi24Cp.Pc.p930 rfl rfl).trans ((runC_node (m := 7) (m2 := 6) (j2 := 933) (Lr := CFSG.KD.Fi24Cp.Pc.l933) ((nodeV_pow (R := AR) (D := SD) (lo := 930) (L := CFSG.KD.Fi24Cp.Pc.l932) (j := 932) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 930 CFSG.KD.Fi24Cp.Pc.l932 (SD.na.getD 932 0)) (SD.nk.getD 932 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Cp.Pc.q932_3 rfl).trans ((powR_seq (n := 3) CFSG.KD.Fi24Cp.Pc.q932_2 rfl).trans ((powR_seq (n := 2) CFSG.KD.Fi24Cp.Pc.q932_1 rfl).trans (powR_last CFSG.KD.Fi24Cp.Pc.r932)))))) (by quickRfl) rfl rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 935) CFSG.KD.Fi24Cp.Pc.p933 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 937) CFSG.KD.Fi24Cp.Pc.p935 rfl rfl)))))).trans CFSG.KD.Fi24Cp.Pc.f69

end
