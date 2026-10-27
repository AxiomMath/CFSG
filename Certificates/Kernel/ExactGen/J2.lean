module

public import CFSG.LocalAnalysis.ComponentClassification.ExactGenJ2Inputs
import Certificates.Kernel.ExactGen.J2Checks
import Certificates.Kernel.LocalComp.K3J2
import CFSG.Certificates.Kernel.ExactGen.Sound
import CFSG.Certificates.Kernel.ExactGen.ParseSound
import CFSG.Certificates.Kernel.Misc.ArrBind

set_option maxRecDepth 1000000

namespace CertificateChecks.KernelEG.J2

open CFSG.ComponentClassification.SolMax.SwapP2.ExactFin
open CFSG.KC.ExactGen CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum

theorem hsz : 0 < 315 ∧ 315 + 1 < 2 ^ 9 ∧ 315 < 65536 := by norm_num

theorem hw : szOK 315 9 = true := by decide

theorem cP : C.ctx.chP.check 315 = true ∧ C.ctx.chP.order 315 = 604800 := by
  obtain ⟨h1, h2⟩ := chain_ok_of hsz hbP kP CP.head CP.hl (by decide +kernel) CP.hs
  exact ⟨h1, h2.trans oP⟩

theorem cN : C.ctx.chN.check 315 = true ∧ C.ctx.chN.order 315 = 1209600 := by
  obtain ⟨h1, h2⟩ := chain_ok_of hsz hbN kN CN.head CN.hl (by decide +kernel) CN.hs
  exact ⟨h1, h2.trans oN⟩

theorem cTN : C.chTN.check 315 = true ∧ C.chTN.order 315 = 256 := by
  obtain ⟨h1, h2⟩ := chain_ok_of hsz hbTN kTN CTN.head CTN.hl (by decide +kernel) CTN.hs
  exact ⟨h1, h2.trans oTN⟩

theorem cC0 : C.reps[0]!.chC.check 315 = true ∧ C.reps[0]!.chC.order 315 = 1920 := by
  obtain ⟨h1, h2⟩ := chain_ok_of hsz hbC0 kC0 CC0.head CC0.hl (by decide +kernel) CC0.hs
  exact ⟨h1, h2.trans oC0⟩

theorem cX0 : C.reps[0]!.chX.check 315 = true ∧ C.reps[0]!.chX.order 315 = 1920 := by
  obtain ⟨h1, h2⟩ := chain_ok_of hsz hbX0 kX0 CX0.head CX0.hl (by decide +kernel) CX0.hs
  exact ⟨h1, h2.trans oX0⟩

theorem cT0 : C.reps[0]!.chT.check 315 = true ∧ C.reps[0]!.chT.order 315 = 128 := by
  obtain ⟨h1, h2⟩ := chain_ok_of hsz hbT0 kT0 CT0.head CT0.hl (by decide +kernel) CT0.hs
  exact ⟨h1, h2.trans oT0⟩

theorem cC1 : C.reps[1]!.chC.check 315 = true ∧ C.reps[1]!.chC.order 315 = 240 := by
  obtain ⟨h1, h2⟩ := chain_ok_of hsz hbC1 kC1 CC1.head CC1.hl (by decide +kernel) CC1.hs
  exact ⟨h1, h2.trans oC1⟩

theorem cX1 : C.reps[1]!.chX.check 315 = true ∧ C.reps[1]!.chX.order 315 = 60 := by
  obtain ⟨h1, h2⟩ := chain_ok_of hsz hbX1 kX1 CX1.head CX1.hl (by decide +kernel) CX1.hs
  exact ⟨h1, h2.trans oX1⟩

theorem cT1 : C.reps[1]!.chT.check 315 = true ∧ C.reps[1]!.chT.order 315 = 4 := by
  obtain ⟨h1, h2⟩ := chain_ok_of hsz hbT1 kT1 CT1.head CT1.hl (by decide +kernel) CT1.hs
  exact ⟨h1, h2.trans oT1⟩

theorem cC2 : C.reps[2]!.chC.check 315 = true ∧ C.reps[2]!.chC.order 315 = 336 := by
  obtain ⟨h1, h2⟩ := chain_ok_of hsz hbC2 kC2 CC2.head CC2.hl (by decide +kernel) CC2.hs
  exact ⟨h1, h2.trans oC2⟩

theorem cX2 : C.reps[2]!.chX.check 315 = true ∧ C.reps[2]!.chX.order 315 = 168 := by
  obtain ⟨h1, h2⟩ := chain_ok_of hsz hbX2 kX2 CX2.head CX2.hl (by decide +kernel) CX2.hs
  exact ⟨h1, h2.trans oX2⟩

theorem cT2 : C.reps[2]!.chT.check 315 = true ∧ C.reps[2]!.chT.order 315 = 8 := by
  obtain ⟨h1, h2⟩ := chain_ok_of hsz hbT2 kT2 CT2.head CT2.hl (by decide +kernel) CT2.hs
  exact ⟨h1, h2.trans oT2⟩

def RO : List RepOrd := [(1920, 1920, 128), (240, 60, 4), (336, 168, 8)]

theorem hR : ∀ j < C.reps.length, RepChains 315 C.reps[j]! RO[j]! := by
  intro j hj
  rw [f11] at hj
  interval_cases j
  · exact ⟨cC0.1, cC0.2, cX0.1, cX0.2, cT0.1, cT0.2⟩
  · exact ⟨cC1.1, cC1.2, cX1.1, cX1.2, cT1.1, cT1.2⟩
  · exact ⟨cC2.1, cC2.2, cX2.1, cX2.2, cT2.1, cT2.2⟩

theorem h12 : ∀ j < C.reps.length,
    repK 315 9 C.ctx C.reps[j]! (BT j) 604800 (RO[j]!).1 (RO[j]!).2.1 (RO[j]!).2.2 = true := by
  intro j hj
  rw [f11] at hj
  interval_cases j
  · exact r0
  · exact r1
  · exact r2

theorem hro : RO.length = C.reps.length := by
  rw [f11]
  rfl

theorem hf4 : ∀ r ∈ C.reps, (chainBK 315 9 r.chC && chainBK 315 9 r.chX && chainBK 315 9 r.chT) =
    true := List.all_eq_true.1 f4

theorem hK : fcK 315 9 C 604800 1209600 256 RO BT = true := by
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

theorem okC : C.ok 315 = true := by
  apply fc_ok_of hw cP.1 cP.2 cN.1 cN.2 cTN.1 cTN.2 hR
  exact hK

theorem parse_eq : j2FC () = C := by
  have e : intsL J2T.chars = J2Tok.head! := by
    rw [← kTok]
    rfl
  unfold j2FC
  rw [J2T.eq, parseFC_eq 315 kTokOK, e]
  rfl

theorem strong_eq {j : Nat} (hj : j < 2) :
    (CFSG.Sporadic.Schreier.PairNative.j2StrongArrs ())[j]! =
      unpack 315 9 (CertificateChecks.KernelLC.K3.J2HX.F j) := by
  unfold CFSG.Sporadic.Schreier.PairNative.j2StrongArrs
  rw [getElem!_pos _ j (by simp; omega), Array.getElem_ofFn,
    CFSG.Sporadic.Schreier.PairNative.j2Strong, CertificateChecks.KernelLC.K3.J2HX.eq]
  exact CFSG.KC.Misc.HexFlat.hexTable_sound CertificateChecks.KernelLC.K3.J2HX.all j hj

theorem kS01 : (arrBind C.ctx.chP.S[0]! 315 9 (CertificateChecks.KernelLC.K3.J2HX.F 0) &&
    arrBind C.ctx.chP.S[1]! 315 9 (CertificateChecks.KernelLC.K3.J2HX.F 1)) = true := by
  decide +kernel

end CertificateChecks.KernelEG.J2

public section

namespace CertificateChecks.KernelEG.J2

open CFSG.ComponentClassification.SolMax.SwapP2.ExactFin

theorem check : j2FCCheck () = true := by
  have h01 := kS01
  rw [Bool.and_eq_true] at h01
  have s0 := (CFSG.KC.Misc.ArrEnum.arrBind_sound h01.1).trans (strong_eq (j := 0) (by norm_num)).symm
  have s1 := (CFSG.KC.Misc.ArrEnum.arrBind_sound h01.2).trans (strong_eq (j := 1) (by norm_num)).symm
  unfold j2FCCheck
  simp only [parse_eq, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  exact ⟨⟨⟨⟨⟨okC, kP⟩, s0⟩, s1⟩, cP.2⟩, cN.2⟩

end CertificateChecks.KernelEG.J2

end
