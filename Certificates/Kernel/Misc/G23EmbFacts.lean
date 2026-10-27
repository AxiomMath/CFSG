module

public import CFSG.Certificates.Kernel.Misc.G23EmbSound
public import CFSG.Certificates.Kernel.Misc.Spec.Cover23
public import CFSG.Certificates.Kernel.Misc.Spec.Payload
public import Certificates.Kernel.Misc.G23Checks
public import Certificates.Kernel.Misc.G23EmbChecks
import CFSG.Certificates.Kernel.Spor.PK.MiscBase

public section

set_option maxRecDepth 100000

namespace CFSG.KD.Misc.G23Emb

open CFSG.KC.Misc.Spec CFSG.KC.Misc.G24 CFSG.KC.Misc.G23 CFSG.KC.Misc.G23Emb CFSG.KD.Misc.G23
open CFSG.LieType.Multipliers.G23 CFSG.CGT.PushingUpLit.CGT6.EmbModule CFSG.Sporadic.He.Native

noncomputable def ML (l : Fin 2 × Bool) : Matrix (Fin 54) (Fin 54) (ZMod 2) := toM (coverLetter l)

theorem decA : decodeK cA = CFSG.KD.Misc.G23.Ab := by
  have h := CFSG.KD.Misc.G23.check
  unfold g23K at h
  simp only [CFSG.KS.PK.andB_eq, Bool.and_eq_true, Nat.beq_eq] at h
  exact h.1

theorem decB : decodeK cB = Bb := by
  have h := CFSG.KD.Misc.G23.check
  unfold g23K at h
  simp only [CFSG.KS.PK.andB_eq, Bool.and_eq_true, Nat.beq_eq] at h
  exact h.2.1

theorem pA (b : Bool) : pkMat 54 CFSG.KD.Misc.G23.Ab = ML (0, b) := by
  rw [← decA, pkMat_decodeK]
  cases b <;> rfl

theorem pB : pkMat 54 Bb = ML (1, true) := by
  rw [← decB, pkMat_decodeK]
  rfl

theorem pBi : pkMat 54 BiK = ML (1, false) := by
  change pkMat 54 (mulF2 54 Bb Bb) = toM (mulM 2 54 coverB coverB)
  rw [pkMat_mulF2, pB, mulM_eq, toM_ofM]
  rfl

theorem nth_RK (j : Fin 4) :
    nthV RK j.val = wordM CFSG.KD.Misc.G23.Ab Bb BiK (encC (genWord j)) := by
  fin_cases j <;> rfl

theorem coverRoot_eq (j : Fin 4) : coverRoot j = ofM (pkMat 54 (nthV RK j.val)) := by
  rw [nth_RK]
  change coverWordArr (genWord j) =
    ofM (pkMat 54 (wordM CFSG.KD.Misc.G23.Ab Bb BiK (encG (genWord j))))
  rw [pkMat_wordM pA pB pBi]
  exact foldr_mulM coverLetter (genWord j)

theorem prodArr_eq (js : List (Fin 4)) :
    prodArr 2 54 coverRoot js = ofM (pkMat 54 (prodK RK (js.map Fin.val))) := by
  induction js with
  | nil =>
    change idM 54 = ofM (pkMat 54 (oneF2 54))
    rw [pkMat_oneF2, idM_eq]
  | cons j js ih =>
    change mulM 2 54 (coverRoot j) (prodArr 2 54 coverRoot js) =
      ofM (pkMat 54 (mulF2 54 (nthV RK j.val) (prodK RK (js.map Fin.val))))
    rw [ih, coverRoot_eq, mulM_eq, toM_ofM, toM_ofM, pkMat_mulF2]

theorem hU : covU = ofM (pkMat 54 UK) := prodArr_eq uW
theorem hV : covV = ofM (pkMat 54 VK) := prodArr_eq vW
theorem hA1 : covA1 = ofM (pkMat 54 A1K) := prodArr_eq a1W
theorem hA2 : covA2 = ofM (pkMat 54 A2K) := prodArr_eq a2W

theorem hC0 : covC0 = ofM (pkMat 54 (c0K UK A2K)) := by
  rw [pkMat_c0K, covC0, hU, hA2]
  simp only [mulM_eq, toM_ofM]

theorem coverEmbCheck_true : coverEmbCheck = true := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := embK_sound check
  unfold coverEmbCheck
  rw [hC0, hU, hV, hA1, hA2]
  simp only [mulM_eq, toM_ofM, idM_eq, entryOf, ofM_zero_one, h1, h2, h3, h4, h5, h6, h7, h8, h9,
    h10, h11, h12, h13, val_one_two, beq_self_eq_true, Bool.and_self]

end CFSG.KD.Misc.G23Emb

end
