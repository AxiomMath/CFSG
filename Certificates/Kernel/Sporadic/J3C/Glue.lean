module

public import Certificates.Kernel.Sporadic.J3C.GlueU
public import Certificates.Kernel.Sporadic.J3C.GlueS

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelSpor.J3CGlue

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.RuSchreier CFSG.Sporadic.Schreier.Co3.Native CFSG.ClassicalInvolution.J3Data
  CFSG.ClassicalInvolution.J3Groups CFSG.KS.CentReg

theorem ab_ok : ∀ h < 2, isInvA 20520 abArr[h]! abInv[h]! = true := isInvAB

theorem sChain_ok : rawChainOK 20520 (sStrong.extract 0 4) sStrong sBase sDeriv 4 = true ∧
    rawOrbitSizes 20520 sStrong sBase = [128, 1, 1] := by
  refine ⟨?_, sSizes⟩
  have hc : Nat.card (Subgroup.closure (Set.range fun j : Fin 4 => permOfArr 20520 sStrong[j.val]!))
      ≤ (rawOrbitSizes 20520 sStrong sBase).prod := by
    have h128 : ([128, 1, 1] : List Nat).prod = 128 := rfl
    rw [sSizes, h128, ← sCard]
    refine Subgroup.card_le_of_le ?_
    rw [Subgroup.closure_le]
    rintro _ ⟨j, rfl⟩
    exact Subgroup.subset_closure ⟨j.val, j.isLt, rfl⟩
  have hW : wordsArr 4 4 CertificateChecks.KernelSchreierFam.J3Cq.sD = sDeriv := by
    decide +kernel
  have h := CFSG.KS.Raw.rawChainK_of_card (chunks := 4)
    CertificateChecks.KernelSchreierFam.J3CqBind.s_binds
    CertificateChecks.KernelSchreierFam.J3Cq.SY.head
    CertificateChecks.KernelSchreierFam.J3Cq.SY.hl hc
  rw [hW] at h
  exact h

theorem centK : Nat.card K = 1920 ∧ (∀ g ∈ K, g * pa = pa * g) ∧
    ∀ g ∈ P, g * pa = pa * g → g ∈ K := by
  refine ⟨kCard, fun g hg => (mem_centIn.1 (kLeC hg)).2, fun g hg hc => ?_⟩
  rw [kFree.1]
  exact mem_centIn.2 ⟨hg, hc⟩

theorem uFacts : K ≤ Subgroup.normalizer (U : Set (Equiv.Perm (Fin 20520))) ∧ Nat.card U = 32 ∧
    ∀ g ∈ K, (∀ u ∈ U, g * u = u * g) → g ∈ U :=
  ⟨kNorm, uCard, kCentU⟩

theorem coverS : ∀ s ∈ S, orderOf s = 2 → ∃ c ∈ P, s = c * pa * c⁻¹ := coverS'

end CertificateChecks.KernelSpor.J3CGlue

end
