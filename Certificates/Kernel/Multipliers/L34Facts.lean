module

public import CFSG.Certificates.Kernel.Misc.Coset.PG
public import Certificates.Kernel.Misc.Coset.XL34R
public import Certificates.Kernel.Misc.Coset.XL34B
public import Certificates.Kernel.Misc.Coset.XL34C
public import Certificates.Kernel.Multipliers.L34Lower
public import CFSG.LieType.Multipliers.L34Data
import all CFSG.LieType.Multipliers.L34Data
import all CFSG.LieType.Multipliers.CoverWords
import all CFSG.Certificates.PresentationLetters
import all CFSG.Certificates.CosetTablePresented
import all CFSG.Fischer.F4

public section

namespace CertificateChecks.KernelL34

open CFSG.CosetTable CFSG.KC.MiscCoset CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34
  CFSG.Certificates.CosetEnumeration CFSG.Fischer

set_option maxRecDepth 100000

theorem mats :
    (aMat.det = 1 ∧ aInvMat.det = 1 ∧ bMat.det = 1 ∧ bInvMat.det = 1)
    ∧ (∀ i j k l : Fin 3, ∀ c : F4, i ≠ j →
      (if k = l then 1 else if k = i ∧ l = j then c else 0) =
      (if k = l then (1 : F4) else 0) + (if i = k ∧ j = l then c else 0))
    ∧ (rels.all (fun r => (wordMat r).isScalar) = true)
    ∧ (coverWs.all (fun r => decide (wordMat r = Mat3.one)) = true)
    ∧ (wordMat zOne = Mat3.one)
    ∧ (wordMat zTwo = Mat3.one)
    ∧ ((wordMat zThree).isScalar = true)
    ∧ (∀ i j : Fin 3, ∀ c : F4, i ≠ j → wordMat (transWord i j c) = transMat i j c)
    ∧ (∀ d₀ d₁ d₂ : F4, d₀ * d₁ * d₂ = 1 →
      wordMat (diagWord d₀ d₁) = diagMat d₀ d₁ d₂) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem tR : rels.map encW = CFSG.KBRoute.XL34R.rels := by decide +kernel
theorem wR : CFSG.KBRoute.XL34R.T1.words = [encW [((1 : Fin 2), true)]] := by decide +kernel
theorem pR : (List.replicate 5 [((1 : Fin 2), true)]).flatten ∈ rels := by decide +kernel

theorem cyclic_card_le : Finite (PG 2 rels) ∧ Nat.card (PG 2 rels) ≤ 20160 := by
  have h := CertificateChecks.KernelMiscCoset.XL34R.t1
  unfold CFSG.KBRoute.XL34R.T1.ok at h
  have hi := zpowers_index_le_of_tableOk rels tR h (by norm_num) CFSG.KBRoute.XL34R.top _ wR
  exact card_le_of_zpowers_index rels _ (by norm_num) pR hi

theorem tB : (restrictWords (subsetOf 2 [1]) coverWs).map encW = CFSG.KBRoute.XL34B.rels := by
  decide +kernel

theorem restrict_card_le :
    Finite (PG (subsetOf 2 [1]).length (restrictWords (subsetOf 2 [1]) coverWs)) ∧
      Nat.card (PG (subsetOf 2 [1]).length (restrictWords (subsetOf 2 [1]) coverWs)) ≤ 5 := by
  have h := CertificateChecks.KernelMiscCoset.XL34B.t1
  unfold CFSG.KBRoute.XL34B.T1.ok at h
  exact card_le_of_tableOk _ tB h (by decide) CFSG.KBRoute.XL34B.top rfl

theorem tC : coverWs.map encW = CFSG.KBRoute.XL34C.rels := by decide +kernel
theorem wC : CFSG.KBRoute.XL34C.T1.words = (subsetOf 2 [1]).map fun x => [(x.val, true)] := by
  decide +kernel

theorem cover_index_walks :
    (genSub {r : FreeGroup (Fin 2) | r ∈ coverWs.map FreeGroup.mk} (subsetOf 2 [1])).FiniteIndex ∧
      (genSub {r : FreeGroup (Fin 2) | r ∈ coverWs.map FreeGroup.mk}
        (subsetOf 2 [1])).index ≤ 193536 ∧
      ∀ p ∈ walkWords, p.2 ∣ orderOf (PresentedGroup.mk
        {r : FreeGroup (Fin 2) | r ∈ coverWs.map FreeGroup.mk} (FreeGroup.mk p.1)) := by
  have h := CertificateChecks.KernelMiscCoset.XL34C.t1
  unfold CFSG.KBRoute.XL34C.T1.ok at h
  obtain ⟨hfi, hidx⟩ := genSub_index_le_of_tableOk coverWs tC h (by norm_num)
    CFSG.KBRoute.XL34C.top _ wC
  exact ⟨hfi, hidx, walks⟩

end CertificateChecks.KernelL34

end
