module

public import Certificates.Kernel.SporSch.Ru.Gens
public import Certificates.Kernel.SporSch.Ru.Pts
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.Ru2247

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.Sporadic.RuSchreier
  CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CertificateChecks.KernelSporSch

theorem l1 : lettersK 2 ruNCenterWord = true := by quickRfl
theorem l2 : lettersK 2 ruSeedWord = true := by quickRfl
theorem l3 : lettersAllK 2 ruSWords = true := by quickRfl
theorem l4 : lettersAllK 2 ruKWords = true := by quickRfl
theorem l5 : lettersAllK 2 ruJWords = true := by quickRfl
theorem l6 : lettersAllK 4 ruRWords = true := by quickRfl

theorem letters : ruWordsLettersOK = true := by
  rw [ruWordsLettersOK, lettersK_sound l1, lettersK_sound l2, lettersAllK_sound l3,
    lettersAllK_sound l4, lettersAllK_sound l5, lettersAllK_sound l6]
  rfl

theorem d1 : derivK ruCGenCount 7 ruCDerivations = true := by quickRfl
theorem d2 : derivK ruNGenCount 6 ruNDerivations = true := by quickRfl
theorem d3 : derivK ruJoinGenCount 18 ruJoinDerivations = true := by quickRfl
theorem d4 : derivK ruCFaithfulGenCount 7 ruCFaithfulDerivations = true := by quickRfl
theorem d5 : derivK ruCQuotient80GenCount 8 ruCQuotient80Derivations = true := by quickRfl
theorem d6 : derivK ruSGenCount 7 ruSDerivations = true := by quickRfl
theorem d7 : derivK ruKGenCount 10 ruKDerivations = true := by quickRfl
theorem d8 : derivK ruJGenCount 10 ruJDerivations = true := by quickRfl
theorem d9 : derivK ruRGenCount 7 ruRDerivations = true := by quickRfl

theorem deriv {k s : Nat} {D : List (List Int)} (h : derivK k s D = true) : ruDerivOK k s D = true :=
  derivK_sound h

theorem facts (htree : ruBytesTree.size = 6 * 593774) : (isInvA 4060 ruA0A (ruInv ruA0A) = true ∧ isInvA 4060 ruA1A (ruInv ruA1A) = true ∧
      ruCRunA.2.2 = true ∧ ruNRunA.2.2 = true ∧ isInvA 4060 ruN0A (ruInv ruN0A) = true ∧
      isInvA 4060 ruN1A (ruInv ruN1A) = true ∧ isInvA 4060 ruC0A (ruInv ruC0A) = true ∧
      isInvA 4060 ruC1A (ruInv ruC1A) = true ∧ isInvA 4060 ruWA (ruInv ruWA) = true ∧
      isInvA 4060 ruHA (ruInv ruHA) = true ∧ isInvA 4060 ruNs0A (ruInv ruNs0A) = true ∧
      isInvA 4060 ruNs1A (ruInv ruNs1A) = true ∧
      (∀ i < 4, isInvA 4060 ruSGensA[i]! (ruInv ruSGensA[i]!) = true) ∧ ruWordsLettersOK = true) ∧
    (ruLayoutOK ruBytes4060 4060 45 = true ∧ ruLayoutOK ruBytes1920 1920 41 = true ∧
      ruLayoutOK ruBytes80 80 8 = true ∧
      (∀ L < 45, isInvA 4060 (ruArr4060 L) (invCand 4060 (ruArr4060 L)) = true) ∧
      (∀ L < 41, isInvA 1920 (ruArr1920 L) (invCand 1920 (ruArr1920 L)) = true) ∧
      (∀ L < 8, isInvA 80 (ruArr80 L) (invCand 80 (ruArr80 L)) = true) ∧
      ruBytesPts.size = 3 * 10120 ∧
      (∀ f < 9, ∀ i < (ruPtsOffsets.getD f (0, 0)).2, (ruPtList f)[i]! < 4060) ∧
      ruBytesTree.size = 6 * 593774 ∧ ruDerivOK ruCGenCount 7 ruCDerivations = true ∧
      ruDerivOK ruNGenCount 6 ruNDerivations = true ∧
      ruDerivOK ruJoinGenCount 18 ruJoinDerivations = true ∧
      ruDerivOK ruCFaithfulGenCount 7 ruCFaithfulDerivations = true ∧
      ruDerivOK ruCQuotient80GenCount 8 ruCQuotient80Derivations = true ∧
      ruDerivOK ruSGenCount 7 ruSDerivations = true ∧ ruDerivOK ruKGenCount 10 ruKDerivations = true ∧
      ruDerivOK ruJGenCount 10 ruJDerivations = true ∧ ruDerivOK ruRGenCount 7 ruRDerivations = true ∧
      (∀ k < 12, ruCSmallPartition.getD k 0 < 6) ∧ (∀ k < 28, ruNSmallPartition.getD k 0 < 7) ∧
      ruCSmallOrbit.length = 12 ∧ ruCSmallPartition.length = 12 ∧ ruNSmallOrbit.length = 28 ∧
      ruNSmallPartition.length = 28 ∧ (∀ x ∈ ruCSmallOrbit, x < 4060) ∧
      (∀ x ∈ ruNSmallOrbit, x < 4060) ∧ (∀ b ∈ ruQuotientBits, b < 8)) := by
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13⟩ := RuG.basic
  obtain ⟨y1, y2, y3⟩ := RuLines.layout
  obtain ⟨i1, i2, i3⟩ := RuLines.isInv
  exact ⟨⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, letters⟩,
    ⟨y1, y2, y3, i1, i2, i3, RuPts.pts.1, RuPts.pts.2, htree, deriv d1, deriv d2, deriv d3,
      deriv d4, deriv d5, deriv d6, deriv d7, deriv d8, deriv d9, by decide, by decide, by decide,
      by decide, by decide, by decide, by decide, by decide, by decide⟩⟩

end CertificateChecks.KernelSporSch.Ru2247

end
