module

public import CFSG.Monster.B.Co2CatalogCheckInputs
public import CFSG.Certificates.Kernel.Co1F2Sound
public import Certificates.Kernel.Sporadic.RawGen
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic
import all Init.Data.Array.Basic
import CFSG.Certificates.Kernel.Common.Harness
public import Mathlib.Tactic.NormNum

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelMonB.Co2SA CFSG.Sporadic.Co2.Native.seedA

#ks_chars CertificateChecks.KernelMonB.Co2SB CFSG.Sporadic.Co2.Native.seedB

public section

namespace CertificateChecks.Bridge3114

open CFSG.Monster.B.Co2Catalog CFSG.Sporadic.SmallF2.Native CFSG.Monster.B.Binary.Native
  CFSG.Monster.B.Max2.Native CFSG.KC.Co1F2 CFSG.KC.M1F2 CertificateChecks.KernelMonB

@[expose] def RA : Nat :=
  25855448750583792323583825853057604051445481365315111270362555824700785334918029535874230004331316089740971902649127431963225864236809393065164802

@[expose] def RB : Nat :=
  21851471752308311268391897182740748439080030833417946906964448090010851972407326561301153682522908381631228222102777496781640673843338863741763588

theorem bindA : m1Bind Co2SA.chars 22 RA = true := by quickRfl

theorem bindB : m1Bind Co2SB.chars 22 RB = true := by quickRfl

theorem catalogRows_zero : catalogRows 0 = unpackR 22 RA := by
  change rowsOfPayload 22 CFSG.Sporadic.Co2.Native.seedA = _
  rw [Co2SA.eq]
  exact bind_sound bindA

theorem catalogRows_one : catalogRows 1 = unpackR 22 RB := by
  change rowsOfPayload 22 CFSG.Sporadic.Co2.Native.seedB = _
  rw [Co2SB.eq]
  exact bind_sound bindB

theorem kRec : bridgeRec.nativeAWord = [15] ∧ bridgeRec.nativeBWord.length = 80 ∧
    (∀ l ∈ bridgeRec.nativeBWord, l ≠ 0 ∧ l.natAbs ≤ 24) ∧
    bridgeRec.nativeRows.length = 2 ∧ bridgeRec.catalogTransposeRows.length = 2 ∧
    bridgeRec.changeOfBasisRows.length = 22 ∧ (∀ x ∈ bridgeRec.changeOfBasisRows, x < 2 ^ 22) := by
  decide +kernel

theorem kQuot : ∀ i < 24, ((quotRows i).size == 22 &&
    mulRows 22 (quotRows i) (inv22 (quotRows i)) == idRows 22) = true := by
  decide +kernel

theorem kWordA : (bridgeWordRows bridgeRec.nativeAWord == bridgeNativeArr 0) = true := by
  decide +kernel

theorem kWordB : (bridgeWordRows bridgeRec.nativeBWord == bridgeNativeArr 1) = true := by
  decide +kernel

theorem kCat0 : (transposeRows 22 (unpackR 22 RA) == bridgeCatalogArr 0) = true := by
  decide +kernel

theorem kCat1 : (transposeRows 22 (unpackR 22 RB) == bridgeCatalogArr 1) = true := by
  decide +kernel

theorem kC : (mulRows 22 bridgeCRows (inv22 bridgeCRows) == idRows 22 &&
    mulRows 22 (bridgeNativeArr 0) bridgeCRows == mulRows 22 bridgeCRows (bridgeCatalogArr 0) &&
    mulRows 22 (bridgeNativeArr 1) bridgeCRows == mulRows 22 bridgeCRows (bridgeCatalogArr 1)) =
      true := by
  decide +kernel

theorem facts : bridgeRec.nativeAWord = [15] ∧ bridgeRec.nativeBWord.length = 80 ∧
    (∀ l ∈ bridgeRec.nativeBWord, l ≠ 0 ∧ l.natAbs ≤ 24) ∧
    bridgeRec.nativeRows.length = 2 ∧ bridgeRec.catalogTransposeRows.length = 2 ∧
    bridgeRec.changeOfBasisRows.length = 22 ∧ (∀ x ∈ bridgeRec.changeOfBasisRows, x < 2 ^ 22) ∧
    (∀ i < 24, (quotRows i).size = 22 ∧
      mulRows 22 (quotRows i) (inv22 (quotRows i)) = idRows 22) ∧
    bridgeWordRows bridgeRec.nativeAWord = bridgeNativeArr 0 ∧
    bridgeWordRows bridgeRec.nativeBWord = bridgeNativeArr 1 ∧
    transposeRows 22 (catalogRows 0) = bridgeCatalogArr 0 ∧
    transposeRows 22 (catalogRows 1) = bridgeCatalogArr 1 ∧
    mulRows 22 bridgeCRows (inv22 bridgeCRows) = idRows 22 ∧
    mulRows 22 (bridgeNativeArr 0) bridgeCRows = mulRows 22 bridgeCRows (bridgeCatalogArr 0) ∧
    mulRows 22 (bridgeNativeArr 1) bridgeCRows = mulRows 22 bridgeCRows (bridgeCatalogArr 1) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := kRec
  have hC := kC
  simp only [Bool.and_eq_true, beq_iff_eq] at hC
  refine ⟨h1, h2, h3, h4, h5, h6, h7, fun i hi => ?_, beq_iff_eq.1 kWordA, beq_iff_eq.1 kWordB,
    ?_, ?_, hC.1.1, hC.1.2, hC.2⟩
  · have h := kQuot i hi
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact h
  · rw [catalogRows_zero]
    exact beq_iff_eq.1 kCat0
  · rw [catalogRows_one]
    exact beq_iff_eq.1 kCat1

end CertificateChecks.Bridge3114

end
