module

public import CFSG.LocalAnalysis.ComponentClassification.ExactGenU35Inputs
import Certificates.Kernel.ExactGen.U35Checks
import CFSG.Certificates.Kernel.ExactGen.Sound
import CFSG.Certificates.Kernel.ExactGen.ParseSound

set_option maxRecDepth 1000000

namespace CertificateChecks.KernelEG.U35

open CFSG.ComponentClassification.SolMax.SwapP2.ExactFin
open CFSG.KC.ExactGen CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum

theorem hsz : 0 < 50 ∧ 50 + 1 < 2 ^ 6 ∧ 50 < 65536 := by norm_num

theorem hw : szOK 50 6 = true := by decide

theorem cP : C.ctx.chP.check 50 = true ∧ C.ctx.chP.order 50 = 126000 := by
  obtain ⟨h1, h2⟩ := chain_ok_of hsz hbP kP CP.head CP.hl (by decide +kernel) CP.hs
  exact ⟨h1, h2.trans oP⟩

theorem cN : C.ctx.chN.check 50 = true ∧ C.ctx.chN.order 50 = 252000 := by
  obtain ⟨h1, h2⟩ := chain_ok_of hsz hbN kN CN.head CN.hl (by decide +kernel) CN.hs
  exact ⟨h1, h2.trans oN⟩

theorem cTN : C.chTN.check 50 = true ∧ C.chTN.order 50 = 32 := by
  obtain ⟨h1, h2⟩ := chain_ok_of hsz hbTN kTN CTN.head CTN.hl (by decide +kernel) CTN.hs
  exact ⟨h1, h2.trans oTN⟩

theorem cC0 : C.reps[0]!.chC.check 50 = true ∧ C.reps[0]!.chC.order 50 = 240 := by
  obtain ⟨h1, h2⟩ := chain_ok_of hsz hbC0 kC0 CC0.head CC0.hl (by decide +kernel) CC0.hs
  exact ⟨h1, h2.trans oC0⟩

theorem cX0 : C.reps[0]!.chX.check 50 = true ∧ C.reps[0]!.chX.order 50 = 120 := by
  obtain ⟨h1, h2⟩ := chain_ok_of hsz hbX0 kX0 CX0.head CX0.hl (by decide +kernel) CX0.hs
  exact ⟨h1, h2.trans oX0⟩

theorem cT0 : C.reps[0]!.chT.check 50 = true ∧ C.reps[0]!.chT.order 50 = 8 := by
  obtain ⟨h1, h2⟩ := chain_ok_of hsz hbT0 kT0 CT0.head CT0.hl (by decide +kernel) CT0.hs
  exact ⟨h1, h2.trans oT0⟩

theorem cC1 : C.reps[1]!.chC.check 50 = true ∧ C.reps[1]!.chC.order 50 = 120 := by
  obtain ⟨h1, h2⟩ := chain_ok_of hsz hbC1 kC1 CC1.head CC1.hl (by decide +kernel) CC1.hs
  exact ⟨h1, h2.trans oC1⟩

theorem cX1 : C.reps[1]!.chX.check 50 = true ∧ C.reps[1]!.chX.order 50 = 60 := by
  obtain ⟨h1, h2⟩ := chain_ok_of hsz hbX1 kX1 CX1.head CX1.hl (by decide +kernel) CX1.hs
  exact ⟨h1, h2.trans oX1⟩

theorem cT1 : C.reps[1]!.chT.check 50 = true ∧ C.reps[1]!.chT.order 50 = 4 := by
  obtain ⟨h1, h2⟩ := chain_ok_of hsz hbT1 kT1 CT1.head CT1.hl (by decide +kernel) CT1.hs
  exact ⟨h1, h2.trans oT1⟩

def RO : List RepOrd := [(240, 120, 8), (120, 60, 4)]

theorem hR : ∀ j < C.reps.length, RepChains 50 C.reps[j]! RO[j]! := by
  intro j hj
  rw [f11] at hj
  interval_cases j
  · exact ⟨cC0.1, cC0.2, cX0.1, cX0.2, cT0.1, cT0.2⟩
  · exact ⟨cC1.1, cC1.2, cX1.1, cX1.2, cT1.1, cT1.2⟩

theorem h12 : ∀ j < C.reps.length,
    repK 50 6 C.ctx C.reps[j]! (BT j) 126000 (RO[j]!).1 (RO[j]!).2.1 (RO[j]!).2.2 = true := by
  intro j hj
  rw [f11] at hj
  interval_cases j
  · exact r0
  · exact r1

theorem hro : RO.length = C.reps.length := by
  rw [f11]
  rfl

theorem hf4 : ∀ r ∈ C.reps, (chainBK 50 6 r.chC && chainBK 50 6 r.chX && chainBK 50 6 r.chT) =
    true := List.all_eq_true.1 f4

theorem hK : fcK 50 6 C 126000 252000 32 RO BT = true := by
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

theorem okC : C.ok 50 = true := by
  apply fc_ok_of hw cP.1 cP.2 cN.1 cN.2 cTN.1 cTN.2 hR
  exact hK

theorem parse_eq : u35FC () = C := by
  have e : intsL PT.chars = PTok.head! := by
    rw [← kTok]
    rfl
  unfold u35FC
  rw [PT.eq, parseFC_eq 50 kTokOK, e]
  rfl

end CertificateChecks.KernelEG.U35

public section

namespace CertificateChecks.KernelEG.U35

open CFSG.ComponentClassification.SolMax.SwapP2.ExactFin

theorem check : u35FCCheck () = true := by
  unfold u35FCCheck
  simp only [parse_eq, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨⟨okC, kP⟩, g01⟩, cP.2⟩, cN.2⟩

end CertificateChecks.KernelEG.U35

end
