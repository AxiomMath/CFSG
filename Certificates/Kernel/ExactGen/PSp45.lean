module

public import CFSG.LocalAnalysis.ComponentClassification.ExactGenPSp45Inputs
import Certificates.Kernel.ExactGen.PSp45Checks
import CFSG.Certificates.Kernel.ExactGen.Sound
import CFSG.Certificates.Kernel.ExactGen.ParseSound

set_option maxRecDepth 1000000

namespace CertificateChecks.KernelEG.PSp45

open CFSG.ComponentClassification.SolMax.SwapP2.ExactFin
open CFSG.KC.ExactGen CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum

theorem hsz : 0 < 156 ∧ 156 + 1 < 2 ^ 8 ∧ 156 < 65536 := by norm_num

theorem hw : szOK 156 8 = true := by decide

theorem cP : C.ctx.chP.check 156 = true ∧ C.ctx.chP.order 156 = 4680000 := by
  obtain ⟨h1, h2⟩ := chain_ok_of hsz hbP kP CP.head CP.hl (by decide +kernel) CP.hs
  exact ⟨h1, h2.trans oP⟩

theorem cN : C.ctx.chN.check 156 = true ∧ C.ctx.chN.order 156 = 9360000 := by
  obtain ⟨h1, h2⟩ := chain_ok_of hsz hbN kN CN.head CN.hl (by decide +kernel) CN.hs
  exact ⟨h1, h2.trans oN⟩

theorem cTN : C.chTN.check 156 = true ∧ C.chTN.order 156 = 128 := by
  obtain ⟨h1, h2⟩ := chain_ok_of hsz hbTN kTN CTN.head CTN.hl (by decide +kernel) CTN.hs
  exact ⟨h1, h2.trans oTN⟩

theorem cC0 : C.reps[0]!.chC.check 156 = true ∧ C.reps[0]!.chC.order 156 = 14400 := by
  obtain ⟨h1, h2⟩ := chain_ok_of hsz hbC0 kC0 CC0.head CC0.hl (by decide +kernel) CC0.hs
  exact ⟨h1, h2.trans oC0⟩

theorem cX0 : C.reps[0]!.chX.check 156 = true ∧ C.reps[0]!.chX.order 156 = 7200 := by
  obtain ⟨h1, h2⟩ := chain_ok_of hsz hbX0 kX0 CX0.head CX0.hl (by decide +kernel) CX0.hs
  exact ⟨h1, h2.trans oX0⟩

theorem cT0 : C.reps[0]!.chT.check 156 = true ∧ C.reps[0]!.chT.order 156 = 32 := by
  obtain ⟨h1, h2⟩ := chain_ok_of hsz hbT0 kT0 CT0.head CT0.hl (by decide +kernel) CT0.hs
  exact ⟨h1, h2.trans oT0⟩

theorem cC1 : C.reps[1]!.chC.check 156 = true ∧ C.reps[1]!.chC.order 156 = 480 := by
  obtain ⟨h1, h2⟩ := chain_ok_of hsz hbC1 kC1 CC1.head CC1.hl (by decide +kernel) CC1.hs
  exact ⟨h1, h2.trans oC1⟩

theorem cX1 : C.reps[1]!.chX.check 156 = true ∧ C.reps[1]!.chX.order 156 = 120 := by
  obtain ⟨h1, h2⟩ := chain_ok_of hsz hbX1 kX1 CX1.head CX1.hl (by decide +kernel) CX1.hs
  exact ⟨h1, h2.trans oX1⟩

theorem cT1 : C.reps[1]!.chT.check 156 = true ∧ C.reps[1]!.chT.order 156 = 8 := by
  obtain ⟨h1, h2⟩ := chain_ok_of hsz hbT1 kT1 CT1.head CT1.hl (by decide +kernel) CT1.hs
  exact ⟨h1, h2.trans oT1⟩

theorem cC2 : C.reps[2]!.chC.check 156 = true ∧ C.reps[2]!.chC.order 156 = 15600 := by
  obtain ⟨h1, h2⟩ := chain_ok_of hsz hbC2 kC2 CC2.head CC2.hl (by decide +kernel) CC2.hs
  exact ⟨h1, h2.trans oC2⟩

theorem cX2 : C.reps[2]!.chX.check 156 = true ∧ C.reps[2]!.chX.order 156 = 7800 := by
  obtain ⟨h1, h2⟩ := chain_ok_of hsz hbX2 kX2 CX2.head CX2.hl (by decide +kernel) CX2.hs
  exact ⟨h1, h2.trans oX2⟩

theorem cT2 : C.reps[2]!.chT.check 156 = true ∧ C.reps[2]!.chT.order 156 = 8 := by
  obtain ⟨h1, h2⟩ := chain_ok_of hsz hbT2 kT2 CT2.head CT2.hl (by decide +kernel) CT2.hs
  exact ⟨h1, h2.trans oT2⟩

theorem cC3 : C.reps[3]!.chC.check 156 = true ∧ C.reps[3]!.chC.order 156 = 720 := by
  obtain ⟨h1, h2⟩ := chain_ok_of hsz hbC3 kC3 CC3.head CC3.hl (by decide +kernel) CC3.hs
  exact ⟨h1, h2.trans oC3⟩

theorem cX3 : C.reps[3]!.chX.check 156 = true ∧ C.reps[3]!.chX.order 156 = 180 := by
  obtain ⟨h1, h2⟩ := chain_ok_of hsz hbX3 kX3 CX3.head CX3.hl (by decide +kernel) CX3.hs
  exact ⟨h1, h2.trans oX3⟩

theorem cT3 : C.reps[3]!.chT.check 156 = true ∧ C.reps[3]!.chT.order 156 = 4 := by
  obtain ⟨h1, h2⟩ := chain_ok_of hsz hbT3 kT3 CT3.head CT3.hl (by decide +kernel) CT3.hs
  exact ⟨h1, h2.trans oT3⟩

def RO : List RepOrd :=
  [(14400, 7200, 32), (480, 120, 8), (15600, 7800, 8), (720, 180, 4)]

theorem hR : ∀ j < C.reps.length, RepChains 156 C.reps[j]! RO[j]! := by
  intro j hj
  rw [f11] at hj
  interval_cases j
  · exact ⟨cC0.1, cC0.2, cX0.1, cX0.2, cT0.1, cT0.2⟩
  · exact ⟨cC1.1, cC1.2, cX1.1, cX1.2, cT1.1, cT1.2⟩
  · exact ⟨cC2.1, cC2.2, cX2.1, cX2.2, cT2.1, cT2.2⟩
  · exact ⟨cC3.1, cC3.2, cX3.1, cX3.2, cT3.1, cT3.2⟩

theorem h12 : ∀ j < C.reps.length,
    repK 156 8 C.ctx C.reps[j]! (BT j) 4680000 (RO[j]!).1 (RO[j]!).2.1 (RO[j]!).2.2 = true := by
  intro j hj
  rw [f11] at hj
  interval_cases j
  · exact r0
  · exact r1
  · exact r2
  · exact r3

theorem hro : RO.length = C.reps.length := by
  rw [f11]
  rfl

theorem hf4 : ∀ r ∈ C.reps, (chainBK 156 8 r.chC && chainBK 156 8 r.chX && chainBK 156 8 r.chT) =
    true := List.all_eq_true.1 f4

theorem hK : fcK 156 8 C 4680000 9360000 128 RO BT = true := by
  apply fcK_of
  · exact f1
  · exact f2
  · exact f3
  · exact hf4
  · exact f5
  · exact f6
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact f10
  · exact hro
  · exact h12

theorem okC : C.ok 156 = true := by
  apply fc_ok_of hw cP.1 cP.2 cN.1 cN.2 cTN.1 cTN.2 hR
  exact hK

theorem parse_eq : psp45FC () = C := by
  have e : intsL PT.chars = PTok.head! := by
    rw [← kTok]
    rfl
  unfold psp45FC
  rw [PT.eq, parseFC_eq 156 kTokOK, e]
  rfl

end CertificateChecks.KernelEG.PSp45

public section

namespace CertificateChecks.KernelEG.PSp45

open CFSG.ComponentClassification.SolMax.SwapP2.ExactFin

theorem check : psp45FCCheck () = true := by
  have h01 := g01
  rw [Bool.and_eq_true] at h01
  unfold psp45FCCheck
  simp only [parse_eq, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨okC, kP⟩, h01.1⟩, h01.2⟩, cP.2⟩, cN.2⟩

end CertificateChecks.KernelEG.PSp45

end
