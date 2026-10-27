
module

public import Certificates.Kernel.UnitarySix.Gen
public import CFSG.Certificates.Kernel.U6Sound
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.NativeDataInputs
public import Certificates.Kernel.UnitarySix.GenEq
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.C9NativeInputsBase
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.HuntClassBraidInputs
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaNativeDataBase

@[expose] public section

#u6_pts CertificateChecks.KernelU6.U

namespace CertificateChecks.KernelU6

open CFSG.KC.U6 CFSG.KLie.CT

theorem kPts :
    ptsOK (fun c => CFSG.F4.Native.hermC c c) CFSG.F4.Native.normC U.UP U.POS = true := by
  quickRfl

theorem kTV : tvOK (fun c => CFSG.F4.Native.weightC c == 2) U.UP U.TV = true := by quickRfl

theorem kI0 : letOK U.UP U.POS U.TV U.LT (0) = true := by quickRfl
theorem kI1 : letOK U.UP U.POS U.TV U.LT (1) = true := by quickRfl
theorem kI2 : letOK U.UP U.POS U.TV U.LT (2) = true := by quickRfl
theorem kI3 : letOK U.UP U.POS U.TV U.LT (3) = true := by quickRfl
theorem kI4 : letOK U.UP U.POS U.TV U.LT (4) = true := by quickRfl
theorem kI5 : letOK U.UP U.POS U.TV U.LT (5) = true := by quickRfl
theorem kI6 : letOK U.UP U.POS U.TV U.LT (6) = true := by quickRfl
theorem kI7 : letOK U.UP U.POS U.TV U.LT (7) = true := by quickRfl
theorem kI8 : letOK U.UP U.POS U.TV U.LT (8) = true := by quickRfl
theorem kI9 : letOK U.UP U.POS U.TV U.LT (9) = true := by quickRfl
theorem kI10 : letOK U.UP U.POS U.TV U.LT (10) = true := by quickRfl
theorem kI11 : letOK U.UP U.POS U.TV U.LT (11) = true := by quickRfl
theorem kI12 : letOK U.UP U.POS U.TV U.LT (12) = true := by quickRfl
theorem kI13 : letOK U.UP U.POS U.TV U.LT (13) = true := by quickRfl
theorem kI14 : letOK U.UP U.POS U.TV U.LT (14) = true := by quickRfl
theorem kI15 : letOK U.UP U.POS U.TV U.LT (15) = true := by quickRfl
theorem kI16 : letOK U.UP U.POS U.TV U.LT (16) = true := by quickRfl
theorem kI17 : letOK U.UP U.POS U.TV U.LT (17) = true := by quickRfl
theorem kI18 : letOK U.UP U.POS U.TV U.LT (18) = true := by quickRfl
theorem kI19 : letOK U.UP U.POS U.TV U.LT (19) = true := by quickRfl
theorem kI20 : letOK U.UP U.POS U.TV U.LT (20) = true := by quickRfl
theorem kI21 : letOK U.UP U.POS U.TV U.LT (21) = true := by quickRfl
theorem kI22 : letOK U.UP U.POS U.TV U.LT (22) = true := by quickRfl
theorem kI23 : letOK U.UP U.POS U.TV U.LT (23) = true := by quickRfl
theorem kI24 : letOK U.UP U.POS U.TV U.LT (24) = true := by quickRfl
theorem kI25 : letOK U.UP U.POS U.TV U.LT (25) = true := by quickRfl
theorem kI26 : letOK U.UP U.POS U.TV U.LT (26) = true := by quickRfl
theorem kI27 : letOK U.UP U.POS U.TV U.LT (27) = true := by quickRfl
theorem kI28 : letOK U.UP U.POS U.TV U.LT (28) = true := by quickRfl
theorem kI29 : letOK U.UP U.POS U.TV U.LT (29) = true := by quickRfl
theorem kI30 : letOK U.UP U.POS U.TV U.LT (30) = true := by quickRfl
theorem kI31 : letOK U.UP U.POS U.TV U.LT (31) = true := by quickRfl
theorem kI32 : letOK U.UP U.POS U.TV U.LT (32) = true := by quickRfl
theorem kI33 : letOK U.UP U.POS U.TV U.LT (33) = true := by quickRfl
theorem kI34 : letOK U.UP U.POS U.TV U.LT (34) = true := by quickRfl
theorem kI35 : letOK U.UP U.POS U.TV U.LT (35) = true := by quickRfl
theorem kI36 : letOK U.UP U.POS U.TV U.LT (36) = true := by quickRfl
theorem kI37 : letOK U.UP U.POS U.TV U.LT (37) = true := by quickRfl
theorem kI38 : letOK U.UP U.POS U.TV U.LT (38) = true := by quickRfl
theorem kI39 : letOK U.UP U.POS U.TV U.LT (39) = true := by quickRfl
theorem kI40 : letOK U.UP U.POS U.TV U.LT (40) = true := by quickRfl
theorem kI41 : letOK U.UP U.POS U.TV U.LT (41) = true := by quickRfl
theorem kI42 : letOK U.UP U.POS U.TV U.LT (42) = true := by quickRfl
theorem kI43 : letOK U.UP U.POS U.TV U.LT (43) = true := by quickRfl
theorem kI44 : letOK U.UP U.POS U.TV U.LT (44) = true := by quickRfl
theorem kI45 : letOK U.UP U.POS U.TV U.LT (45) = true := by quickRfl

theorem kLet : ∀ k < 46, letOK U.UP U.POS U.TV U.LT k = true := by
  intro k hk
  interval_cases k
  exacts [kI0, kI1, kI2, kI3, kI4, kI5, kI6, kI7, kI8, kI9, kI10, kI11, kI12, kI13, kI14, kI15,
    kI16, kI17, kI18, kI19, kI20, kI21, kI22, kI23, kI24, kI25, kI26, kI27, kI28, kI29, kI30, kI31,
    kI32, kI33, kI34, kI35, kI36, kI37, kI38, kI39, kI40, kI41, kI42, kI43, kI44, kI45]

theorem kNe : ∀ k < 46, ∃ p < 693, ap10 (letK U.LT k) p ≠ p := by decide +kernel

theorem up_eq : decA U.UP 12 693 = CFSG.F4.Native.uPts := (pts_sound kPts).1

theorem pos_eq : decA U.POS 10 4096 = CFSG.F4.Native.uPos := by
  rw [(pts_sound kPts).2, up_eq]
  rfl

theorem tv_eq : decA U.TV 12 46 = CFSG.F4.Native.tvGens := by
  rw [tv_sound kTV, up_eq]
  rfl

theorem natAbs_succ_sub (k : ℕ) : ((k : ℤ) + 1).natAbs - 1 = k := by omega

open CFSG.EvenSmallLie.UnitarySix in
theorem cert3180 : ∀ k < 46, involOK (letterT k) = true :=
  fun k hk => by rw [letterT_eq]; exact sound3180 up_eq pos_eq tv_eq kLet kNe k hk

end CertificateChecks.KernelU6

end
