module

public import Certificates.Kernel.I242.YData
public import CFSG.Certificates.Kernel.Spor.RawPos
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelI242.YP

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw
open CertificateChecks.KernelI242

@[expose] noncomputable def SP (i s : Nat) : Prop :=
  schPK 3510 12 Y.S Y.SI Y.LR Y.TR Y.TRI 17 8 Y.BP 7 i (s * 1) 1 = true

theorem sp0_0 : SP 0 0 := by unfold SP; quickRfl
theorem sp0_1 : SP 0 1 := by unfold SP; quickRfl
theorem sp0_2 : SP 0 2 := by unfold SP; quickRfl
theorem sp0_3 : SP 0 3 := by unfold SP; quickRfl
theorem sp0_4 : SP 0 4 := by unfold SP; quickRfl
theorem sp0_5 : SP 0 5 := by unfold SP; quickRfl
theorem sp0_6 : SP 0 6 := by unfold SP; quickRfl
theorem sp0_7 : SP 0 7 := by unfold SP; quickRfl
theorem sp0_8 : SP 0 8 := by unfold SP; quickRfl
theorem sp0_9 : SP 0 9 := by unfold SP; quickRfl
theorem sp0_10 : SP 0 10 := by unfold SP; quickRfl
theorem sp0_11 : SP 0 11 := by unfold SP; quickRfl
theorem sp0_12 : SP 0 12 := by unfold SP; quickRfl
theorem sp0_13 : SP 0 13 := by unfold SP; quickRfl
theorem sp0_14 : SP 0 14 := by unfold SP; quickRfl
theorem sp0_15 : SP 0 15 := by unfold SP; quickRfl
theorem sp0_16 : SP 0 16 := by unfold SP; quickRfl
theorem sp0_17 : SP 0 17 := by unfold SP; quickRfl
theorem sp0_18 : SP 0 18 := by unfold SP; quickRfl
theorem sp0_19 : SP 0 19 := by unfold SP; quickRfl
theorem sp0_20 : SP 0 20 := by unfold SP; quickRfl
theorem sp0_21 : SP 0 21 := by unfold SP; quickRfl
theorem sp0_22 : SP 0 22 := by unfold SP; quickRfl
theorem sp0_23 : SP 0 23 := by unfold SP; quickRfl
theorem sp0_24 : SP 0 24 := by unfold SP; quickRfl
theorem sp0_25 : SP 0 25 := by unfold SP; quickRfl
theorem sp0_26 : SP 0 26 := by unfold SP; quickRfl
theorem sp0_27 : SP 0 27 := by unfold SP; quickRfl
theorem sp0_28 : SP 0 28 := by unfold SP; quickRfl
theorem sp0_29 : SP 0 29 := by unfold SP; quickRfl
theorem sp0_30 : SP 0 30 := by unfold SP; quickRfl
theorem sp0_31 : SP 0 31 := by unfold SP; quickRfl
theorem sp0_32 : SP 0 32 := by unfold SP; quickRfl
theorem sp0_33 : SP 0 33 := by unfold SP; quickRfl
theorem sp0_34 : SP 0 34 := by unfold SP; quickRfl
theorem sp0_35 : SP 0 35 := by unfold SP; quickRfl
theorem sp0_36 : SP 0 36 := by unfold SP; quickRfl
theorem sp0_37 : SP 0 37 := by unfold SP; quickRfl
theorem sp0_38 : SP 0 38 := by unfold SP; quickRfl
theorem sp0_39 : SP 0 39 := by unfold SP; quickRfl
theorem sp0_40 : SP 0 40 := by unfold SP; quickRfl
theorem sp0_41 : SP 0 41 := by unfold SP; quickRfl
theorem sp0_42 : SP 0 42 := by unfold SP; quickRfl
theorem sp0_43 : SP 0 43 := by unfold SP; quickRfl
theorem sp0_44 : SP 0 44 := by unfold SP; quickRfl
theorem sp0_45 : SP 0 45 := by unfold SP; quickRfl
theorem sp0_46 : SP 0 46 := by unfold SP; quickRfl
theorem sp0_47 : SP 0 47 := by unfold SP; quickRfl
theorem sp0_48 : SP 0 48 := by unfold SP; quickRfl
theorem sp0_49 : SP 0 49 := by unfold SP; quickRfl
theorem sp0_50 : SP 0 50 := by unfold SP; quickRfl
theorem sp0_51 : SP 0 51 := by unfold SP; quickRfl
theorem sp0_52 : SP 0 52 := by unfold SP; quickRfl
theorem sp0_53 : SP 0 53 := by unfold SP; quickRfl
theorem sp0_54 : SP 0 54 := by unfold SP; quickRfl
theorem sp0_55 : SP 0 55 := by unfold SP; quickRfl
theorem sp0_56 : SP 0 56 := by unfold SP; quickRfl
theorem sp0_57 : SP 0 57 := by unfold SP; quickRfl
theorem sp0_58 : SP 0 58 := by unfold SP; quickRfl
theorem sp0_59 : SP 0 59 := by unfold SP; quickRfl
theorem sp0_60 : SP 0 60 := by unfold SP; quickRfl
theorem sp0_61 : SP 0 61 := by unfold SP; quickRfl
theorem sp0_62 : SP 0 62 := by unfold SP; quickRfl
theorem sp0_63 : SP 0 63 := by unfold SP; quickRfl
theorem sp0_64 : SP 0 64 := by unfold SP; quickRfl
theorem sp0_65 : SP 0 65 := by unfold SP; quickRfl
theorem sp0_66 : SP 0 66 := by unfold SP; quickRfl
theorem sp0_67 : SP 0 67 := by unfold SP; quickRfl
theorem sp0_68 : SP 0 68 := by unfold SP; quickRfl
theorem sp0_69 : SP 0 69 := by unfold SP; quickRfl
theorem sp0_70 : SP 0 70 := by unfold SP; quickRfl
theorem sp0_71 : SP 0 71 := by unfold SP; quickRfl
theorem sp0_72 : SP 0 72 := by unfold SP; quickRfl
theorem sp0_73 : SP 0 73 := by unfold SP; quickRfl
theorem sp0_74 : SP 0 74 := by unfold SP; quickRfl
theorem sp0_75 : SP 0 75 := by unfold SP; quickRfl
theorem sp0_76 : SP 0 76 := by unfold SP; quickRfl
theorem sp0_77 : SP 0 77 := by unfold SP; quickRfl
theorem sp0_78 : SP 0 78 := by unfold SP; quickRfl
theorem sp0_79 : SP 0 79 := by unfold SP; quickRfl
theorem sp0_80 : SP 0 80 := by unfold SP; quickRfl
theorem sp0_81 : SP 0 81 := by unfold SP; quickRfl
theorem sp0_82 : SP 0 82 := by unfold SP; quickRfl
theorem sp0_83 : SP 0 83 := by unfold SP; quickRfl
theorem sp0_84 : SP 0 84 := by unfold SP; quickRfl
theorem sp0_85 : SP 0 85 := by unfold SP; quickRfl
theorem sp0_86 : SP 0 86 := by unfold SP; quickRfl
theorem sp0_87 : SP 0 87 := by unfold SP; quickRfl
theorem sp0_88 : SP 0 88 := by unfold SP; quickRfl
theorem sp0_89 : SP 0 89 := by unfold SP; quickRfl
theorem sp0_90 : SP 0 90 := by unfold SP; quickRfl
theorem sp0_91 : SP 0 91 := by unfold SP; quickRfl
theorem sp0_92 : SP 0 92 := by unfold SP; quickRfl
theorem sp0_93 : SP 0 93 := by unfold SP; quickRfl
theorem sp0_94 : SP 0 94 := by unfold SP; quickRfl
theorem sp0_95 : SP 0 95 := by unfold SP; quickRfl
theorem sp0_96 : SP 0 96 := by unfold SP; quickRfl
theorem sp0_97 : SP 0 97 := by unfold SP; quickRfl
theorem sp0_98 : SP 0 98 := by unfold SP; quickRfl
theorem sp0_99 : SP 0 99 := by unfold SP; quickRfl
theorem sp0_100 : SP 0 100 := by unfold SP; quickRfl
theorem sp0_101 : SP 0 101 := by unfold SP; quickRfl
theorem sp0_102 : SP 0 102 := by unfold SP; quickRfl
theorem sp0_103 : SP 0 103 := by unfold SP; quickRfl
theorem sp0_104 : SP 0 104 := by unfold SP; quickRfl
theorem sp0_105 : SP 0 105 := by unfold SP; quickRfl
theorem sp0_106 : SP 0 106 := by unfold SP; quickRfl
theorem sp0_107 : SP 0 107 := by unfold SP; quickRfl
theorem sp0_108 : SP 0 108 := by unfold SP; quickRfl
theorem sp0_109 : SP 0 109 := by unfold SP; quickRfl
theorem sp0_110 : SP 0 110 := by unfold SP; quickRfl
theorem sp0_111 : SP 0 111 := by unfold SP; quickRfl
theorem sp0_112 : SP 0 112 := by unfold SP; quickRfl
theorem sp0_113 : SP 0 113 := by unfold SP; quickRfl
theorem sp0_114 : SP 0 114 := by unfold SP; quickRfl
theorem sp0_115 : SP 0 115 := by unfold SP; quickRfl
theorem sp0_116 : SP 0 116 := by unfold SP; quickRfl
theorem sp0_117 : SP 0 117 := by unfold SP; quickRfl
theorem sp0_118 : SP 0 118 := by unfold SP; quickRfl
theorem sp0_119 : SP 0 119 := by unfold SP; quickRfl
theorem sp1_0 : SP 1 0 := by unfold SP; quickRfl
theorem sp1_1 : SP 1 1 := by unfold SP; quickRfl
theorem sp1_2 : SP 1 2 := by unfold SP; quickRfl
theorem sp1_3 : SP 1 3 := by unfold SP; quickRfl
theorem sp1_4 : SP 1 4 := by unfold SP; quickRfl
theorem sp1_5 : SP 1 5 := by unfold SP; quickRfl
theorem sp1_6 : SP 1 6 := by unfold SP; quickRfl
theorem sp1_7 : SP 1 7 := by unfold SP; quickRfl
theorem sp1_8 : SP 1 8 := by unfold SP; quickRfl
theorem sp1_9 : SP 1 9 := by unfold SP; quickRfl
theorem sp1_10 : SP 1 10 := by unfold SP; quickRfl
theorem sp1_11 : SP 1 11 := by unfold SP; quickRfl
theorem sp1_12 : SP 1 12 := by unfold SP; quickRfl
theorem sp1_13 : SP 1 13 := by unfold SP; quickRfl
theorem sp1_14 : SP 1 14 := by unfold SP; quickRfl
theorem sp1_15 : SP 1 15 := by unfold SP; quickRfl
theorem sp1_16 : SP 1 16 := by unfold SP; quickRfl
theorem sp1_17 : SP 1 17 := by unfold SP; quickRfl
theorem sp1_18 : SP 1 18 := by unfold SP; quickRfl
theorem sp1_19 : SP 1 19 := by unfold SP; quickRfl
theorem sp1_20 : SP 1 20 := by unfold SP; quickRfl
theorem sp1_21 : SP 1 21 := by unfold SP; quickRfl
theorem sp1_22 : SP 1 22 := by unfold SP; quickRfl
theorem sp1_23 : SP 1 23 := by unfold SP; quickRfl
theorem sp1_24 : SP 1 24 := by unfold SP; quickRfl
theorem sp1_25 : SP 1 25 := by unfold SP; quickRfl
theorem sp1_26 : SP 1 26 := by unfold SP; quickRfl
theorem sp1_27 : SP 1 27 := by unfold SP; quickRfl
theorem sp1_28 : SP 1 28 := by unfold SP; quickRfl
theorem sp1_29 : SP 1 29 := by unfold SP; quickRfl
theorem sp1_30 : SP 1 30 := by unfold SP; quickRfl
theorem sp1_31 : SP 1 31 := by unfold SP; quickRfl
theorem sp1_32 : SP 1 32 := by unfold SP; quickRfl
theorem sp1_33 : SP 1 33 := by unfold SP; quickRfl
theorem sp1_34 : SP 1 34 := by unfold SP; quickRfl
theorem sp1_35 : SP 1 35 := by unfold SP; quickRfl
theorem sp1_36 : SP 1 36 := by unfold SP; quickRfl
theorem sp1_37 : SP 1 37 := by unfold SP; quickRfl
theorem sp1_38 : SP 1 38 := by unfold SP; quickRfl
theorem sp1_39 : SP 1 39 := by unfold SP; quickRfl
theorem sp1_40 : SP 1 40 := by unfold SP; quickRfl
theorem sp1_41 : SP 1 41 := by unfold SP; quickRfl
theorem sp1_42 : SP 1 42 := by unfold SP; quickRfl
theorem sp1_43 : SP 1 43 := by unfold SP; quickRfl
theorem sp1_44 : SP 1 44 := by unfold SP; quickRfl
theorem sp1_45 : SP 1 45 := by unfold SP; quickRfl
theorem sp1_46 : SP 1 46 := by unfold SP; quickRfl
theorem sp1_47 : SP 1 47 := by unfold SP; quickRfl
theorem sp1_48 : SP 1 48 := by unfold SP; quickRfl
theorem sp1_49 : SP 1 49 := by unfold SP; quickRfl
theorem sp1_50 : SP 1 50 := by unfold SP; quickRfl
theorem sp1_51 : SP 1 51 := by unfold SP; quickRfl
theorem sp1_52 : SP 1 52 := by unfold SP; quickRfl
theorem sp1_53 : SP 1 53 := by unfold SP; quickRfl
theorem sp1_54 : SP 1 54 := by unfold SP; quickRfl
theorem sp1_55 : SP 1 55 := by unfold SP; quickRfl
theorem sp1_56 : SP 1 56 := by unfold SP; quickRfl
theorem sp1_57 : SP 1 57 := by unfold SP; quickRfl
theorem sp1_58 : SP 1 58 := by unfold SP; quickRfl
theorem sp1_59 : SP 1 59 := by unfold SP; quickRfl
theorem sp1_60 : SP 1 60 := by unfold SP; quickRfl
theorem sp1_61 : SP 1 61 := by unfold SP; quickRfl
theorem sp1_62 : SP 1 62 := by unfold SP; quickRfl
theorem sp2_0 : SP 2 0 := by unfold SP; quickRfl
theorem sp2_1 : SP 2 1 := by unfold SP; quickRfl
theorem sp2_2 : SP 2 2 := by unfold SP; quickRfl
theorem sp2_3 : SP 2 3 := by unfold SP; quickRfl
theorem sp2_4 : SP 2 4 := by unfold SP; quickRfl
theorem sp2_5 : SP 2 5 := by unfold SP; quickRfl
theorem sp2_6 : SP 2 6 := by unfold SP; quickRfl
theorem sp2_7 : SP 2 7 := by unfold SP; quickRfl
theorem sp2_8 : SP 2 8 := by unfold SP; quickRfl
theorem sp2_9 : SP 2 9 := by unfold SP; quickRfl
theorem sp2_10 : SP 2 10 := by unfold SP; quickRfl
theorem sp2_11 : SP 2 11 := by unfold SP; quickRfl
theorem sp2_12 : SP 2 12 := by unfold SP; quickRfl
theorem sp2_13 : SP 2 13 := by unfold SP; quickRfl
theorem sp2_14 : SP 2 14 := by unfold SP; quickRfl
theorem sp2_15 : SP 2 15 := by unfold SP; quickRfl
theorem sp2_16 : SP 2 16 := by unfold SP; quickRfl
theorem sp2_17 : SP 2 17 := by unfold SP; quickRfl
theorem sp2_18 : SP 2 18 := by unfold SP; quickRfl
theorem sp2_19 : SP 2 19 := by unfold SP; quickRfl
theorem sp2_20 : SP 2 20 := by unfold SP; quickRfl
theorem sp2_21 : SP 2 21 := by unfold SP; quickRfl
theorem sp2_22 : SP 2 22 := by unfold SP; quickRfl
theorem sp2_23 : SP 2 23 := by unfold SP; quickRfl
theorem sp2_24 : SP 2 24 := by unfold SP; quickRfl
theorem sp2_25 : SP 2 25 := by unfold SP; quickRfl
theorem sp2_26 : SP 2 26 := by unfold SP; quickRfl
theorem sp2_27 : SP 2 27 := by unfold SP; quickRfl
theorem sp2_28 : SP 2 28 := by unfold SP; quickRfl
theorem sp2_29 : SP 2 29 := by unfold SP; quickRfl
theorem sp3_0 : SP 3 0 := by unfold SP; quickRfl
theorem sp3_1 : SP 3 1 := by unfold SP; quickRfl
theorem sp3_2 : SP 3 2 := by unfold SP; quickRfl
theorem sp3_3 : SP 3 3 := by unfold SP; quickRfl
theorem sp3_4 : SP 3 4 := by unfold SP; quickRfl
theorem sp3_5 : SP 3 5 := by unfold SP; quickRfl
theorem sp3_6 : SP 3 6 := by unfold SP; quickRfl
theorem sp3_7 : SP 3 7 := by unfold SP; quickRfl
theorem sp3_8 : SP 3 8 := by unfold SP; quickRfl
theorem sp3_9 : SP 3 9 := by unfold SP; quickRfl
theorem sp3_10 : SP 3 10 := by unfold SP; quickRfl
theorem sp3_11 : SP 3 11 := by unfold SP; quickRfl
theorem sp4_0 : SP 4 0 := by unfold SP; quickRfl
theorem sp4_1 : SP 4 1 := by unfold SP; quickRfl
theorem sp4_2 : SP 4 2 := by unfold SP; quickRfl
theorem sp4_3 : SP 4 3 := by unfold SP; quickRfl
theorem sp4_4 : SP 4 4 := by unfold SP; quickRfl
theorem sp4_5 : SP 4 5 := by unfold SP; quickRfl
theorem sp4_6 : SP 4 6 := by unfold SP; quickRfl
theorem sp4_7 : SP 4 7 := by unfold SP; quickRfl
theorem sp5_0 : SP 5 0 := by unfold SP; quickRfl
theorem sp5_1 : SP 5 1 := by unfold SP; quickRfl
theorem sp5_2 : SP 5 2 := by unfold SP; quickRfl
theorem sp5_3 : SP 5 3 := by unfold SP; quickRfl
theorem sp6_0 : SP 6 0 := by unfold SP; quickRfl
theorem sp6_1 : SP 6 1 := by unfold SP; quickRfl

theorem spL {i N : Nat} (hc : Nat.ble (rcnt (Y.LR i)) (N * 1) = true)
    (h : ∀ s < N, SP i s) : ∀ s < 3510, SP i s :=
  schK_slices (Nat.le_of_ble_eq_true hc) h

theorem spAll : ∀ i < 7, ∀ s < 3510, SP i s := by
  intro i hi
  interval_cases i
  · refine spL (N := 120) rfl fun s hs => ?_
    interval_cases s
    exacts [sp0_0, sp0_1, sp0_2, sp0_3, sp0_4, sp0_5, sp0_6, sp0_7, sp0_8, sp0_9, sp0_10, sp0_11,
      sp0_12, sp0_13, sp0_14, sp0_15, sp0_16, sp0_17, sp0_18, sp0_19, sp0_20, sp0_21, sp0_22,
      sp0_23, sp0_24, sp0_25, sp0_26, sp0_27, sp0_28, sp0_29, sp0_30, sp0_31, sp0_32, sp0_33,
      sp0_34, sp0_35, sp0_36, sp0_37, sp0_38, sp0_39, sp0_40, sp0_41, sp0_42, sp0_43, sp0_44,
      sp0_45, sp0_46, sp0_47, sp0_48, sp0_49, sp0_50, sp0_51, sp0_52, sp0_53, sp0_54, sp0_55,
      sp0_56, sp0_57, sp0_58, sp0_59, sp0_60, sp0_61, sp0_62, sp0_63, sp0_64, sp0_65, sp0_66,
      sp0_67, sp0_68, sp0_69, sp0_70, sp0_71, sp0_72, sp0_73, sp0_74, sp0_75, sp0_76, sp0_77,
      sp0_78, sp0_79, sp0_80, sp0_81, sp0_82, sp0_83, sp0_84, sp0_85, sp0_86, sp0_87, sp0_88,
      sp0_89, sp0_90, sp0_91, sp0_92, sp0_93, sp0_94, sp0_95, sp0_96, sp0_97, sp0_98, sp0_99,
      sp0_100, sp0_101, sp0_102, sp0_103, sp0_104, sp0_105, sp0_106, sp0_107, sp0_108, sp0_109,
      sp0_110, sp0_111, sp0_112, sp0_113, sp0_114, sp0_115, sp0_116, sp0_117, sp0_118, sp0_119]
  · refine spL (N := 63) rfl fun s hs => ?_
    interval_cases s
    exacts [sp1_0, sp1_1, sp1_2, sp1_3, sp1_4, sp1_5, sp1_6, sp1_7, sp1_8, sp1_9, sp1_10, sp1_11,
      sp1_12, sp1_13, sp1_14, sp1_15, sp1_16, sp1_17, sp1_18, sp1_19, sp1_20, sp1_21, sp1_22,
      sp1_23, sp1_24, sp1_25, sp1_26, sp1_27, sp1_28, sp1_29, sp1_30, sp1_31, sp1_32, sp1_33,
      sp1_34, sp1_35, sp1_36, sp1_37, sp1_38, sp1_39, sp1_40, sp1_41, sp1_42, sp1_43, sp1_44,
      sp1_45, sp1_46, sp1_47, sp1_48, sp1_49, sp1_50, sp1_51, sp1_52, sp1_53, sp1_54, sp1_55,
      sp1_56, sp1_57, sp1_58, sp1_59, sp1_60, sp1_61, sp1_62]
  · refine spL (N := 30) rfl fun s hs => ?_
    interval_cases s
    exacts [sp2_0, sp2_1, sp2_2, sp2_3, sp2_4, sp2_5, sp2_6, sp2_7, sp2_8, sp2_9, sp2_10, sp2_11,
      sp2_12, sp2_13, sp2_14, sp2_15, sp2_16, sp2_17, sp2_18, sp2_19, sp2_20, sp2_21, sp2_22,
      sp2_23, sp2_24, sp2_25, sp2_26, sp2_27, sp2_28, sp2_29]
  · refine spL (N := 12) rfl fun s hs => ?_
    interval_cases s
    exacts [sp3_0, sp3_1, sp3_2, sp3_3, sp3_4, sp3_5, sp3_6, sp3_7, sp3_8, sp3_9, sp3_10, sp3_11]
  · refine spL (N := 8) rfl fun s hs => ?_
    interval_cases s
    exacts [sp4_0, sp4_1, sp4_2, sp4_3, sp4_4, sp4_5, sp4_6, sp4_7]
  · refine spL (N := 4) rfl fun s hs => ?_
    interval_cases s
    exacts [sp5_0, sp5_1, sp5_2, sp5_3]
  · refine spL (N := 2) rfl fun s hs => ?_
    interval_cases s
    exacts [sp6_0, sp6_1]

end CertificateChecks.KernelI242.YP

end
