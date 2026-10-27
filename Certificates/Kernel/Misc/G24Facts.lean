module

public import CFSG.Certificates.Kernel.Misc.G24Sound
public import Certificates.Kernel.Misc.G24Checks

public section

set_option maxRecDepth 100000

namespace CFSG.KD.Misc.G24

open CFSG.KC.Misc.G24 CFSG.LieType.Multipliers.G24 CFSG.Quasithin.G2U CFSG.Fischer

theorem bG : genRows = GR.map (List.map strOf) := rfl
theorem bR : relStrings = RS.map strOf := rfl
theorem bP : pairStrings = PS.map (List.map fun p => (strOf p.1, strOf p.2)) := rfl
theorem bX : genStringsX = XS.map strOf := rfl
theorem bY : genStringsY = YS.map strOf := rfl
theorem bL : liftRows = LR.map (List.map strOf) := rfl

theorem bXL (i : Fin CFSG.Blueprint.Chevalley.Tag.G2.rank) (c : F4) :
    digitRows (XMat F4 i c) = nthLL XL (4 * i.val + c.code.val) := by
  obtain ⟨c⟩ := c
  fin_cases i <;> fin_cases c <;> decide +kernel

theorem bYL (i : Fin CFSG.Blueprint.Chevalley.Tag.G2.rank) (c : F4) :
    digitRows (YMat F4 i c) = nthLL YL (4 * i.val + c.code.val) := by
  obtain ⟨c⟩ := c
  fin_cases i <;> fin_cases c <;> decide +kernel

theorem facts44 : (invCheck = true) ∧ (relCheck = true) ∧ (commCheck = true) ∧
    (rootCheck = true) ∧ (suzCheck = true) := by
  have h := g24F4_sound bG bR bP bX bY bXL bYL k44
  rw [invCheck_eq, relCheck_eq, commCheck_eq, rootCheck_eq]
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, suz⟩

theorem facts45 : (unitCheck = true) ∧ (coverCheck = true) ∧ (kerCheck = true) := by
  rw [unitCheck_eq, coverCheck_eq, kerCheck_eq]
  exact g24F3_sound bL bR bP k45

end CFSG.KD.Misc.G24

end
