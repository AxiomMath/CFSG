module

public import Certificates.Kernel.OmegaEight.Forms
public import Certificates.Data.Kernel.O8.Orth

public section

namespace CertificateChecks.KernelO8

open CFSG.KC.O8

@[expose] def LP : List ℕ := [0, 1152, 1152, 1152, 1152, 1152, 1152, 1152, 1152, 1152, 1152,
  1152, 0, 0, 0, 0, 1152, 1152, 0, 0, 1152, 1152, 0, 0, 1152, 1152, 0, 0, 0, 0, 1152, 1152, 1152,
  0, 1152, 0, 1152, 0, 1152, 0, 1152, 0, 1152, 0, 0, 1152, 0, 1152, 1152, 0, 0, 1152, 1152, 0, 0,
  1152, 1152, 0, 0, 1152, 0, 1152, 1152, 0]

@[expose] def LM : List ℕ := [0, 1920, 1920, 1920, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1920, 1920,
  0, 0, 0, 0, 1920, 1920, 0, 0, 1920, 1920, 0, 0, 1920, 1920, 1920, 0, 1920, 0, 0, 1920, 0, 1920,
  0, 1920, 0, 1920, 0, 1920, 0, 1920, 1920, 0, 0, 1920, 0, 1920, 1920, 0, 0, 1920, 1920, 0, 0,
  1920, 1920, 0]

theorem kCntP_0 : walkFrom QP (fun _ => 1) 0 = 0 := by decide +kernel
theorem kCntP_1 : walkFrom QP (fun _ => 1) 1 = 1152 := by decide +kernel
theorem kCntP_2 : walkFrom QP (fun _ => 1) 2 = 1152 := by decide +kernel
theorem kCntP_3 : walkFrom QP (fun _ => 1) 3 = 1152 := by decide +kernel
theorem kCntP_4 : walkFrom QP (fun _ => 1) 4 = 1152 := by decide +kernel
theorem kCntP_5 : walkFrom QP (fun _ => 1) 5 = 1152 := by decide +kernel
theorem kCntP_6 : walkFrom QP (fun _ => 1) 6 = 1152 := by decide +kernel
theorem kCntP_7 : walkFrom QP (fun _ => 1) 7 = 1152 := by decide +kernel
theorem kCntP_8 : walkFrom QP (fun _ => 1) 8 = 1152 := by decide +kernel
theorem kCntP_9 : walkFrom QP (fun _ => 1) 9 = 1152 := by decide +kernel
theorem kCntP_10 : walkFrom QP (fun _ => 1) 10 = 1152 := by decide +kernel
theorem kCntP_11 : walkFrom QP (fun _ => 1) 11 = 1152 := by decide +kernel
theorem kCntP_12 : walkFrom QP (fun _ => 1) 12 = 0 := by decide +kernel
theorem kCntP_13 : walkFrom QP (fun _ => 1) 13 = 0 := by decide +kernel
theorem kCntP_14 : walkFrom QP (fun _ => 1) 14 = 0 := by decide +kernel
theorem kCntP_15 : walkFrom QP (fun _ => 1) 15 = 0 := by decide +kernel
theorem kCntP_16 : walkFrom QP (fun _ => 1) 16 = 1152 := by decide +kernel
theorem kCntP_17 : walkFrom QP (fun _ => 1) 17 = 1152 := by decide +kernel
theorem kCntP_18 : walkFrom QP (fun _ => 1) 18 = 0 := by decide +kernel
theorem kCntP_19 : walkFrom QP (fun _ => 1) 19 = 0 := by decide +kernel
theorem kCntP_20 : walkFrom QP (fun _ => 1) 20 = 1152 := by decide +kernel
theorem kCntP_21 : walkFrom QP (fun _ => 1) 21 = 1152 := by decide +kernel
theorem kCntP_22 : walkFrom QP (fun _ => 1) 22 = 0 := by decide +kernel
theorem kCntP_23 : walkFrom QP (fun _ => 1) 23 = 0 := by decide +kernel
theorem kCntP_24 : walkFrom QP (fun _ => 1) 24 = 1152 := by decide +kernel
theorem kCntP_25 : walkFrom QP (fun _ => 1) 25 = 1152 := by decide +kernel
theorem kCntP_26 : walkFrom QP (fun _ => 1) 26 = 0 := by decide +kernel
theorem kCntP_27 : walkFrom QP (fun _ => 1) 27 = 0 := by decide +kernel
theorem kCntP_28 : walkFrom QP (fun _ => 1) 28 = 0 := by decide +kernel
theorem kCntP_29 : walkFrom QP (fun _ => 1) 29 = 0 := by decide +kernel
theorem kCntP_30 : walkFrom QP (fun _ => 1) 30 = 1152 := by decide +kernel
theorem kCntP_31 : walkFrom QP (fun _ => 1) 31 = 1152 := by decide +kernel
theorem kCntP_32 : walkFrom QP (fun _ => 1) 32 = 1152 := by decide +kernel
theorem kCntP_33 : walkFrom QP (fun _ => 1) 33 = 0 := by decide +kernel
theorem kCntP_34 : walkFrom QP (fun _ => 1) 34 = 1152 := by decide +kernel
theorem kCntP_35 : walkFrom QP (fun _ => 1) 35 = 0 := by decide +kernel
theorem kCntP_36 : walkFrom QP (fun _ => 1) 36 = 1152 := by decide +kernel
theorem kCntP_37 : walkFrom QP (fun _ => 1) 37 = 0 := by decide +kernel
theorem kCntP_38 : walkFrom QP (fun _ => 1) 38 = 1152 := by decide +kernel
theorem kCntP_39 : walkFrom QP (fun _ => 1) 39 = 0 := by decide +kernel
theorem kCntP_40 : walkFrom QP (fun _ => 1) 40 = 1152 := by decide +kernel
theorem kCntP_41 : walkFrom QP (fun _ => 1) 41 = 0 := by decide +kernel
theorem kCntP_42 : walkFrom QP (fun _ => 1) 42 = 1152 := by decide +kernel
theorem kCntP_43 : walkFrom QP (fun _ => 1) 43 = 0 := by decide +kernel
theorem kCntP_44 : walkFrom QP (fun _ => 1) 44 = 0 := by decide +kernel
theorem kCntP_45 : walkFrom QP (fun _ => 1) 45 = 1152 := by decide +kernel
theorem kCntP_46 : walkFrom QP (fun _ => 1) 46 = 0 := by decide +kernel
theorem kCntP_47 : walkFrom QP (fun _ => 1) 47 = 1152 := by decide +kernel
theorem kCntP_48 : walkFrom QP (fun _ => 1) 48 = 1152 := by decide +kernel
theorem kCntP_49 : walkFrom QP (fun _ => 1) 49 = 0 := by decide +kernel
theorem kCntP_50 : walkFrom QP (fun _ => 1) 50 = 0 := by decide +kernel
theorem kCntP_51 : walkFrom QP (fun _ => 1) 51 = 1152 := by decide +kernel
theorem kCntP_52 : walkFrom QP (fun _ => 1) 52 = 1152 := by decide +kernel
theorem kCntP_53 : walkFrom QP (fun _ => 1) 53 = 0 := by decide +kernel
theorem kCntP_54 : walkFrom QP (fun _ => 1) 54 = 0 := by decide +kernel
theorem kCntP_55 : walkFrom QP (fun _ => 1) 55 = 1152 := by decide +kernel
theorem kCntP_56 : walkFrom QP (fun _ => 1) 56 = 1152 := by decide +kernel
theorem kCntP_57 : walkFrom QP (fun _ => 1) 57 = 0 := by decide +kernel
theorem kCntP_58 : walkFrom QP (fun _ => 1) 58 = 0 := by decide +kernel
theorem kCntP_59 : walkFrom QP (fun _ => 1) 59 = 1152 := by decide +kernel
theorem kCntP_60 : walkFrom QP (fun _ => 1) 60 = 0 := by decide +kernel
theorem kCntP_61 : walkFrom QP (fun _ => 1) 61 = 1152 := by decide +kernel
theorem kCntP_62 : walkFrom QP (fun _ => 1) 62 = 1152 := by decide +kernel
theorem kCntP_63 : walkFrom QP (fun _ => 1) 63 = 0 := by decide +kernel

theorem kInvP_0 : walkFrom QP invBadK 0 = 0 := by decide +kernel
theorem kInvP_1 : walkFrom QP invBadK 1 = 0 := by decide +kernel
theorem kInvP_2 : walkFrom QP invBadK 2 = 0 := by decide +kernel
theorem kInvP_3 : walkFrom QP invBadK 3 = 0 := by decide +kernel
theorem kInvP_4 : walkFrom QP invBadK 4 = 0 := by decide +kernel
theorem kInvP_5 : walkFrom QP invBadK 5 = 0 := by decide +kernel
theorem kInvP_6 : walkFrom QP invBadK 6 = 0 := by decide +kernel
theorem kInvP_7 : walkFrom QP invBadK 7 = 0 := by decide +kernel
theorem kInvP_8 : walkFrom QP invBadK 8 = 0 := by decide +kernel
theorem kInvP_9 : walkFrom QP invBadK 9 = 0 := by decide +kernel
theorem kInvP_10 : walkFrom QP invBadK 10 = 0 := by decide +kernel
theorem kInvP_11 : walkFrom QP invBadK 11 = 0 := by decide +kernel
theorem kInvP_12 : walkFrom QP invBadK 12 = 0 := by decide +kernel
theorem kInvP_13 : walkFrom QP invBadK 13 = 0 := by decide +kernel
theorem kInvP_14 : walkFrom QP invBadK 14 = 0 := by decide +kernel
theorem kInvP_15 : walkFrom QP invBadK 15 = 0 := by decide +kernel
theorem kInvP_16 : walkFrom QP invBadK 16 = 0 := by decide +kernel
theorem kInvP_17 : walkFrom QP invBadK 17 = 0 := by decide +kernel
theorem kInvP_18 : walkFrom QP invBadK 18 = 0 := by decide +kernel
theorem kInvP_19 : walkFrom QP invBadK 19 = 0 := by decide +kernel
theorem kInvP_20 : walkFrom QP invBadK 20 = 0 := by decide +kernel
theorem kInvP_21 : walkFrom QP invBadK 21 = 0 := by decide +kernel
theorem kInvP_22 : walkFrom QP invBadK 22 = 0 := by decide +kernel
theorem kInvP_23 : walkFrom QP invBadK 23 = 0 := by decide +kernel
theorem kInvP_24 : walkFrom QP invBadK 24 = 0 := by decide +kernel
theorem kInvP_25 : walkFrom QP invBadK 25 = 0 := by decide +kernel
theorem kInvP_26 : walkFrom QP invBadK 26 = 0 := by decide +kernel
theorem kInvP_27 : walkFrom QP invBadK 27 = 0 := by decide +kernel
theorem kInvP_28 : walkFrom QP invBadK 28 = 0 := by decide +kernel
theorem kInvP_29 : walkFrom QP invBadK 29 = 0 := by decide +kernel
theorem kInvP_30 : walkFrom QP invBadK 30 = 0 := by decide +kernel
theorem kInvP_31 : walkFrom QP invBadK 31 = 0 := by decide +kernel
theorem kInvP_32 : walkFrom QP invBadK 32 = 0 := by decide +kernel
theorem kInvP_33 : walkFrom QP invBadK 33 = 0 := by decide +kernel
theorem kInvP_34 : walkFrom QP invBadK 34 = 0 := by decide +kernel
theorem kInvP_35 : walkFrom QP invBadK 35 = 0 := by decide +kernel
theorem kInvP_36 : walkFrom QP invBadK 36 = 0 := by decide +kernel
theorem kInvP_37 : walkFrom QP invBadK 37 = 0 := by decide +kernel
theorem kInvP_38 : walkFrom QP invBadK 38 = 0 := by decide +kernel
theorem kInvP_39 : walkFrom QP invBadK 39 = 0 := by decide +kernel
theorem kInvP_40 : walkFrom QP invBadK 40 = 0 := by decide +kernel
theorem kInvP_41 : walkFrom QP invBadK 41 = 0 := by decide +kernel
theorem kInvP_42 : walkFrom QP invBadK 42 = 0 := by decide +kernel
theorem kInvP_43 : walkFrom QP invBadK 43 = 0 := by decide +kernel
theorem kInvP_44 : walkFrom QP invBadK 44 = 0 := by decide +kernel
theorem kInvP_45 : walkFrom QP invBadK 45 = 0 := by decide +kernel
theorem kInvP_46 : walkFrom QP invBadK 46 = 0 := by decide +kernel
theorem kInvP_47 : walkFrom QP invBadK 47 = 0 := by decide +kernel
theorem kInvP_48 : walkFrom QP invBadK 48 = 0 := by decide +kernel
theorem kInvP_49 : walkFrom QP invBadK 49 = 0 := by decide +kernel
theorem kInvP_50 : walkFrom QP invBadK 50 = 0 := by decide +kernel
theorem kInvP_51 : walkFrom QP invBadK 51 = 0 := by decide +kernel
theorem kInvP_52 : walkFrom QP invBadK 52 = 0 := by decide +kernel
theorem kInvP_53 : walkFrom QP invBadK 53 = 0 := by decide +kernel
theorem kInvP_54 : walkFrom QP invBadK 54 = 0 := by decide +kernel
theorem kInvP_55 : walkFrom QP invBadK 55 = 0 := by decide +kernel
theorem kInvP_56 : walkFrom QP invBadK 56 = 0 := by decide +kernel
theorem kInvP_57 : walkFrom QP invBadK 57 = 0 := by decide +kernel
theorem kInvP_58 : walkFrom QP invBadK 58 = 0 := by decide +kernel
theorem kInvP_59 : walkFrom QP invBadK 59 = 0 := by decide +kernel
theorem kInvP_60 : walkFrom QP invBadK 60 = 0 := by decide +kernel
theorem kInvP_61 : walkFrom QP invBadK 61 = 0 := by decide +kernel
theorem kInvP_62 : walkFrom QP invBadK 62 = 0 := by decide +kernel
theorem kInvP_63 : walkFrom QP invBadK 63 = 0 := by decide +kernel

theorem kCntP : ∀ c < 64, walkFrom QP (fun _ => 1) c = LP.getD c 0 := by
  intro c hc
  interval_cases c
  exacts [kCntP_0, kCntP_1, kCntP_2, kCntP_3, kCntP_4, kCntP_5, kCntP_6, kCntP_7, kCntP_8, kCntP_9,
    kCntP_10, kCntP_11, kCntP_12, kCntP_13, kCntP_14, kCntP_15, kCntP_16, kCntP_17, kCntP_18,
    kCntP_19, kCntP_20, kCntP_21, kCntP_22, kCntP_23, kCntP_24, kCntP_25, kCntP_26, kCntP_27,
    kCntP_28, kCntP_29, kCntP_30, kCntP_31, kCntP_32, kCntP_33, kCntP_34, kCntP_35, kCntP_36,
    kCntP_37, kCntP_38, kCntP_39, kCntP_40, kCntP_41, kCntP_42, kCntP_43, kCntP_44, kCntP_45,
    kCntP_46, kCntP_47, kCntP_48, kCntP_49, kCntP_50, kCntP_51, kCntP_52, kCntP_53, kCntP_54,
    kCntP_55, kCntP_56, kCntP_57, kCntP_58, kCntP_59, kCntP_60, kCntP_61, kCntP_62, kCntP_63]

theorem kInvP : ∀ c < 64, walkFrom QP invBadK c = 0 := by
  intro c hc
  interval_cases c
  exacts [kInvP_0, kInvP_1, kInvP_2, kInvP_3, kInvP_4, kInvP_5, kInvP_6, kInvP_7, kInvP_8, kInvP_9,
    kInvP_10, kInvP_11, kInvP_12, kInvP_13, kInvP_14, kInvP_15, kInvP_16, kInvP_17, kInvP_18,
    kInvP_19, kInvP_20, kInvP_21, kInvP_22, kInvP_23, kInvP_24, kInvP_25, kInvP_26, kInvP_27,
    kInvP_28, kInvP_29, kInvP_30, kInvP_31, kInvP_32, kInvP_33, kInvP_34, kInvP_35, kInvP_36,
    kInvP_37, kInvP_38, kInvP_39, kInvP_40, kInvP_41, kInvP_42, kInvP_43, kInvP_44, kInvP_45,
    kInvP_46, kInvP_47, kInvP_48, kInvP_49, kInvP_50, kInvP_51, kInvP_52, kInvP_53, kInvP_54,
    kInvP_55, kInvP_56, kInvP_57, kInvP_58, kInvP_59, kInvP_60, kInvP_61, kInvP_62, kInvP_63]

theorem kCntM_0 : walkFrom QM (fun _ => 1) 0 = 0 := by decide +kernel
theorem kCntM_1 : walkFrom QM (fun _ => 1) 1 = 1920 := by decide +kernel
theorem kCntM_2 : walkFrom QM (fun _ => 1) 2 = 1920 := by decide +kernel
theorem kCntM_3 : walkFrom QM (fun _ => 1) 3 = 1920 := by decide +kernel
theorem kCntM_4 : walkFrom QM (fun _ => 1) 4 = 0 := by decide +kernel
theorem kCntM_5 : walkFrom QM (fun _ => 1) 5 = 0 := by decide +kernel
theorem kCntM_6 : walkFrom QM (fun _ => 1) 6 = 0 := by decide +kernel
theorem kCntM_7 : walkFrom QM (fun _ => 1) 7 = 0 := by decide +kernel
theorem kCntM_8 : walkFrom QM (fun _ => 1) 8 = 0 := by decide +kernel
theorem kCntM_9 : walkFrom QM (fun _ => 1) 9 = 0 := by decide +kernel
theorem kCntM_10 : walkFrom QM (fun _ => 1) 10 = 0 := by decide +kernel
theorem kCntM_11 : walkFrom QM (fun _ => 1) 11 = 0 := by decide +kernel
theorem kCntM_12 : walkFrom QM (fun _ => 1) 12 = 0 := by decide +kernel
theorem kCntM_13 : walkFrom QM (fun _ => 1) 13 = 0 := by decide +kernel
theorem kCntM_14 : walkFrom QM (fun _ => 1) 14 = 0 := by decide +kernel
theorem kCntM_15 : walkFrom QM (fun _ => 1) 15 = 0 := by decide +kernel
theorem kCntM_16 : walkFrom QM (fun _ => 1) 16 = 1920 := by decide +kernel
theorem kCntM_17 : walkFrom QM (fun _ => 1) 17 = 1920 := by decide +kernel
theorem kCntM_18 : walkFrom QM (fun _ => 1) 18 = 0 := by decide +kernel
theorem kCntM_19 : walkFrom QM (fun _ => 1) 19 = 0 := by decide +kernel
theorem kCntM_20 : walkFrom QM (fun _ => 1) 20 = 0 := by decide +kernel
theorem kCntM_21 : walkFrom QM (fun _ => 1) 21 = 0 := by decide +kernel
theorem kCntM_22 : walkFrom QM (fun _ => 1) 22 = 1920 := by decide +kernel
theorem kCntM_23 : walkFrom QM (fun _ => 1) 23 = 1920 := by decide +kernel
theorem kCntM_24 : walkFrom QM (fun _ => 1) 24 = 0 := by decide +kernel
theorem kCntM_25 : walkFrom QM (fun _ => 1) 25 = 0 := by decide +kernel
theorem kCntM_26 : walkFrom QM (fun _ => 1) 26 = 1920 := by decide +kernel
theorem kCntM_27 : walkFrom QM (fun _ => 1) 27 = 1920 := by decide +kernel
theorem kCntM_28 : walkFrom QM (fun _ => 1) 28 = 0 := by decide +kernel
theorem kCntM_29 : walkFrom QM (fun _ => 1) 29 = 0 := by decide +kernel
theorem kCntM_30 : walkFrom QM (fun _ => 1) 30 = 1920 := by decide +kernel
theorem kCntM_31 : walkFrom QM (fun _ => 1) 31 = 1920 := by decide +kernel
theorem kCntM_32 : walkFrom QM (fun _ => 1) 32 = 1920 := by decide +kernel
theorem kCntM_33 : walkFrom QM (fun _ => 1) 33 = 0 := by decide +kernel
theorem kCntM_34 : walkFrom QM (fun _ => 1) 34 = 1920 := by decide +kernel
theorem kCntM_35 : walkFrom QM (fun _ => 1) 35 = 0 := by decide +kernel
theorem kCntM_36 : walkFrom QM (fun _ => 1) 36 = 0 := by decide +kernel
theorem kCntM_37 : walkFrom QM (fun _ => 1) 37 = 1920 := by decide +kernel
theorem kCntM_38 : walkFrom QM (fun _ => 1) 38 = 0 := by decide +kernel
theorem kCntM_39 : walkFrom QM (fun _ => 1) 39 = 1920 := by decide +kernel
theorem kCntM_40 : walkFrom QM (fun _ => 1) 40 = 0 := by decide +kernel
theorem kCntM_41 : walkFrom QM (fun _ => 1) 41 = 1920 := by decide +kernel
theorem kCntM_42 : walkFrom QM (fun _ => 1) 42 = 0 := by decide +kernel
theorem kCntM_43 : walkFrom QM (fun _ => 1) 43 = 1920 := by decide +kernel
theorem kCntM_44 : walkFrom QM (fun _ => 1) 44 = 0 := by decide +kernel
theorem kCntM_45 : walkFrom QM (fun _ => 1) 45 = 1920 := by decide +kernel
theorem kCntM_46 : walkFrom QM (fun _ => 1) 46 = 0 := by decide +kernel
theorem kCntM_47 : walkFrom QM (fun _ => 1) 47 = 1920 := by decide +kernel
theorem kCntM_48 : walkFrom QM (fun _ => 1) 48 = 1920 := by decide +kernel
theorem kCntM_49 : walkFrom QM (fun _ => 1) 49 = 0 := by decide +kernel
theorem kCntM_50 : walkFrom QM (fun _ => 1) 50 = 0 := by decide +kernel
theorem kCntM_51 : walkFrom QM (fun _ => 1) 51 = 1920 := by decide +kernel
theorem kCntM_52 : walkFrom QM (fun _ => 1) 52 = 0 := by decide +kernel
theorem kCntM_53 : walkFrom QM (fun _ => 1) 53 = 1920 := by decide +kernel
theorem kCntM_54 : walkFrom QM (fun _ => 1) 54 = 1920 := by decide +kernel
theorem kCntM_55 : walkFrom QM (fun _ => 1) 55 = 0 := by decide +kernel
theorem kCntM_56 : walkFrom QM (fun _ => 1) 56 = 0 := by decide +kernel
theorem kCntM_57 : walkFrom QM (fun _ => 1) 57 = 1920 := by decide +kernel
theorem kCntM_58 : walkFrom QM (fun _ => 1) 58 = 1920 := by decide +kernel
theorem kCntM_59 : walkFrom QM (fun _ => 1) 59 = 0 := by decide +kernel
theorem kCntM_60 : walkFrom QM (fun _ => 1) 60 = 0 := by decide +kernel
theorem kCntM_61 : walkFrom QM (fun _ => 1) 61 = 1920 := by decide +kernel
theorem kCntM_62 : walkFrom QM (fun _ => 1) 62 = 1920 := by decide +kernel
theorem kCntM_63 : walkFrom QM (fun _ => 1) 63 = 0 := by decide +kernel

theorem kInvM_0 : walkFrom QM invBadK 0 = 0 := by decide +kernel
theorem kInvM_1 : walkFrom QM invBadK 1 = 0 := by decide +kernel
theorem kInvM_2 : walkFrom QM invBadK 2 = 0 := by decide +kernel
theorem kInvM_3 : walkFrom QM invBadK 3 = 0 := by decide +kernel
theorem kInvM_4 : walkFrom QM invBadK 4 = 0 := by decide +kernel
theorem kInvM_5 : walkFrom QM invBadK 5 = 0 := by decide +kernel
theorem kInvM_6 : walkFrom QM invBadK 6 = 0 := by decide +kernel
theorem kInvM_7 : walkFrom QM invBadK 7 = 0 := by decide +kernel
theorem kInvM_8 : walkFrom QM invBadK 8 = 0 := by decide +kernel
theorem kInvM_9 : walkFrom QM invBadK 9 = 0 := by decide +kernel
theorem kInvM_10 : walkFrom QM invBadK 10 = 0 := by decide +kernel
theorem kInvM_11 : walkFrom QM invBadK 11 = 0 := by decide +kernel
theorem kInvM_12 : walkFrom QM invBadK 12 = 0 := by decide +kernel
theorem kInvM_13 : walkFrom QM invBadK 13 = 0 := by decide +kernel
theorem kInvM_14 : walkFrom QM invBadK 14 = 0 := by decide +kernel
theorem kInvM_15 : walkFrom QM invBadK 15 = 0 := by decide +kernel
theorem kInvM_16 : walkFrom QM invBadK 16 = 0 := by decide +kernel
theorem kInvM_17 : walkFrom QM invBadK 17 = 0 := by decide +kernel
theorem kInvM_18 : walkFrom QM invBadK 18 = 0 := by decide +kernel
theorem kInvM_19 : walkFrom QM invBadK 19 = 0 := by decide +kernel
theorem kInvM_20 : walkFrom QM invBadK 20 = 0 := by decide +kernel
theorem kInvM_21 : walkFrom QM invBadK 21 = 0 := by decide +kernel
theorem kInvM_22 : walkFrom QM invBadK 22 = 0 := by decide +kernel
theorem kInvM_23 : walkFrom QM invBadK 23 = 0 := by decide +kernel
theorem kInvM_24 : walkFrom QM invBadK 24 = 0 := by decide +kernel
theorem kInvM_25 : walkFrom QM invBadK 25 = 0 := by decide +kernel
theorem kInvM_26 : walkFrom QM invBadK 26 = 0 := by decide +kernel
theorem kInvM_27 : walkFrom QM invBadK 27 = 0 := by decide +kernel
theorem kInvM_28 : walkFrom QM invBadK 28 = 0 := by decide +kernel
theorem kInvM_29 : walkFrom QM invBadK 29 = 0 := by decide +kernel
theorem kInvM_30 : walkFrom QM invBadK 30 = 0 := by decide +kernel
theorem kInvM_31 : walkFrom QM invBadK 31 = 0 := by decide +kernel
theorem kInvM_32 : walkFrom QM invBadK 32 = 0 := by decide +kernel
theorem kInvM_33 : walkFrom QM invBadK 33 = 0 := by decide +kernel
theorem kInvM_34 : walkFrom QM invBadK 34 = 0 := by decide +kernel
theorem kInvM_35 : walkFrom QM invBadK 35 = 0 := by decide +kernel
theorem kInvM_36 : walkFrom QM invBadK 36 = 0 := by decide +kernel
theorem kInvM_37 : walkFrom QM invBadK 37 = 0 := by decide +kernel
theorem kInvM_38 : walkFrom QM invBadK 38 = 0 := by decide +kernel
theorem kInvM_39 : walkFrom QM invBadK 39 = 0 := by decide +kernel
theorem kInvM_40 : walkFrom QM invBadK 40 = 0 := by decide +kernel
theorem kInvM_41 : walkFrom QM invBadK 41 = 0 := by decide +kernel
theorem kInvM_42 : walkFrom QM invBadK 42 = 0 := by decide +kernel
theorem kInvM_43 : walkFrom QM invBadK 43 = 0 := by decide +kernel
theorem kInvM_44 : walkFrom QM invBadK 44 = 0 := by decide +kernel
theorem kInvM_45 : walkFrom QM invBadK 45 = 0 := by decide +kernel
theorem kInvM_46 : walkFrom QM invBadK 46 = 0 := by decide +kernel
theorem kInvM_47 : walkFrom QM invBadK 47 = 0 := by decide +kernel
theorem kInvM_48 : walkFrom QM invBadK 48 = 0 := by decide +kernel
theorem kInvM_49 : walkFrom QM invBadK 49 = 0 := by decide +kernel
theorem kInvM_50 : walkFrom QM invBadK 50 = 0 := by decide +kernel
theorem kInvM_51 : walkFrom QM invBadK 51 = 0 := by decide +kernel
theorem kInvM_52 : walkFrom QM invBadK 52 = 0 := by decide +kernel
theorem kInvM_53 : walkFrom QM invBadK 53 = 0 := by decide +kernel
theorem kInvM_54 : walkFrom QM invBadK 54 = 0 := by decide +kernel
theorem kInvM_55 : walkFrom QM invBadK 55 = 0 := by decide +kernel
theorem kInvM_56 : walkFrom QM invBadK 56 = 0 := by decide +kernel
theorem kInvM_57 : walkFrom QM invBadK 57 = 0 := by decide +kernel
theorem kInvM_58 : walkFrom QM invBadK 58 = 0 := by decide +kernel
theorem kInvM_59 : walkFrom QM invBadK 59 = 0 := by decide +kernel
theorem kInvM_60 : walkFrom QM invBadK 60 = 0 := by decide +kernel
theorem kInvM_61 : walkFrom QM invBadK 61 = 0 := by decide +kernel
theorem kInvM_62 : walkFrom QM invBadK 62 = 0 := by decide +kernel
theorem kInvM_63 : walkFrom QM invBadK 63 = 0 := by decide +kernel

theorem kCntM : ∀ c < 64, walkFrom QM (fun _ => 1) c = LM.getD c 0 := by
  intro c hc
  interval_cases c
  exacts [kCntM_0, kCntM_1, kCntM_2, kCntM_3, kCntM_4, kCntM_5, kCntM_6, kCntM_7, kCntM_8, kCntM_9,
    kCntM_10, kCntM_11, kCntM_12, kCntM_13, kCntM_14, kCntM_15, kCntM_16, kCntM_17, kCntM_18,
    kCntM_19, kCntM_20, kCntM_21, kCntM_22, kCntM_23, kCntM_24, kCntM_25, kCntM_26, kCntM_27,
    kCntM_28, kCntM_29, kCntM_30, kCntM_31, kCntM_32, kCntM_33, kCntM_34, kCntM_35, kCntM_36,
    kCntM_37, kCntM_38, kCntM_39, kCntM_40, kCntM_41, kCntM_42, kCntM_43, kCntM_44, kCntM_45,
    kCntM_46, kCntM_47, kCntM_48, kCntM_49, kCntM_50, kCntM_51, kCntM_52, kCntM_53, kCntM_54,
    kCntM_55, kCntM_56, kCntM_57, kCntM_58, kCntM_59, kCntM_60, kCntM_61, kCntM_62, kCntM_63]

theorem kInvM : ∀ c < 64, walkFrom QM invBadK c = 0 := by
  intro c hc
  interval_cases c
  exacts [kInvM_0, kInvM_1, kInvM_2, kInvM_3, kInvM_4, kInvM_5, kInvM_6, kInvM_7, kInvM_8, kInvM_9,
    kInvM_10, kInvM_11, kInvM_12, kInvM_13, kInvM_14, kInvM_15, kInvM_16, kInvM_17, kInvM_18,
    kInvM_19, kInvM_20, kInvM_21, kInvM_22, kInvM_23, kInvM_24, kInvM_25, kInvM_26, kInvM_27,
    kInvM_28, kInvM_29, kInvM_30, kInvM_31, kInvM_32, kInvM_33, kInvM_34, kInvM_35, kInvM_36,
    kInvM_37, kInvM_38, kInvM_39, kInvM_40, kInvM_41, kInvM_42, kInvM_43, kInvM_44, kInvM_45,
    kInvM_46, kInvM_47, kInvM_48, kInvM_49, kInvM_50, kInvM_51, kInvM_52, kInvM_53, kInvM_54,
    kInvM_55, kInvM_56, kInvM_57, kInvM_58, kInvM_59, kInvM_60, kInvM_61, kInvM_62, kInvM_63]

end CertificateChecks.KernelO8

end
