module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlp
public import CFSG.HardMathSupport.Dickson.Sec6.Up34SporAux.ThThreeInputs
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabThCensusInputs
public import Certificates.Certificate1020
public import Certificates.Certificate1021
import Certificates.Kernel.ThCensus.Facts
import Certificates.Kernel.ThCensus.Pin
import Certificates.Kernel.ThCent.Consumers
import CFSG.Certificates.Kernel.ThCent.PinSound
import CFSG.Certificates.Kernel.Th.Spec.DceMat
import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThLocalSound
import CFSG.Sporadic.Th.Max3.AllConjFinal
public import CFSG.Perm.CentralizerOrbit
public import CFSG.Sporadic.Ly.ThreeBCount
public import CFSG.Sporadic.Th.CertificateBase
public import CFSG.Sporadic.Th.CertificateBase1
public import CFSG.Sporadic.ThSchreier.FullAutCoreBase
public import CFSG.Sporadic.ThSchreier.KernelAutBase
public import CFSG.Sporadic.ThSchreier.KernelAutBase1
import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThCentSoundBase2
import CFSG.Sporadic.ThSchreier.KernelAut

public section

namespace CertificateChecks.KernelThCensus

open CFSG.Sporadic.Th CFSG.KC.Th CFSG.KC.ThCent CFSG.KC.Th.Spec CFSG.KC.Th.Spec.FwdRel
  CFSG.KD.ThCensus CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlp
open scoped Pointwise

local notation "𝕄" g:max =>
  ((Subtype.val g : GL (Fin 248) (ZMod 2)) : Matrix (Fin 248) (Fin 248) (ZMod 2))


noncomputable def matHom17305 : ↥J →* Matrix (Fin 248) (Fin 248) (ZMod 2) :=
  (Units.coeHom (Matrix (Fin 248) (Fin 248) (ZMod 2))).comp J.subtype

theorem th_census17305 :
    orderOf (slpJ a b CFSG.HardMathSupport.Dickson.Sec6.Up34Th.ThThreeNative.prog3 11) = 3 ∧
      orderOf ThCent.zJ = 3 ∧
      orderOf (slpJ a b CFSG.HardMathSupport.Dickson.I271.TabThNative.progU 22) = 3 ∧
      ∀ x : ↥J, orderOf x = 3 → ∃ k c : ↥J,
        (c = slpJ a b CFSG.HardMathSupport.Dickson.Sec6.Up34Th.ThThreeNative.prog3 11 ∨
          c = ThCent.zJ ∨
          c = slpJ a b CFSG.HardMathSupport.Dickson.I271.TabThNative.progU 22) ∧
        ∃ e : ℕ, (e = 1 ∨ e = 2) ∧ k * c ^ e * k⁻¹ = x := by
  have hfin : Finite ↥J :=
    Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Th.Max3.natCard_J]; norm_num)
  obtain ⟨hA, hB, -, hk⟩ := KernelThCent.fwd_mats
  obtain ⟨h1, hJ⟩ := Dce.andB_iff.1 ch17305J
  obtain ⟨h2, hJ⟩ := Dce.andB_iff.1 hJ
  obtain ⟨hz, hJ⟩ := Dce.andB_iff.1 hJ
  obtain ⟨hs, hu⟩ := Dce.andB_iff.1 hJ
  have ha : matHom17305 a = pkMat (RB 1) := by
    rw [Nat.eq_of_beq_eq_true h1]
    exact hA
  have hb : matHom17305 b = pkMat (RB 2) := by
    rw [Nat.eq_of_beq_eq_true h2]
    exact hB
  have hZ : matHom17305 ThCent.zJ = pkMat (RB regZ) := by
    rw [Nat.eq_of_beq_eq_true hz]
    exact KernelThCent.mat_zJ
  have hS : matHom17305 (slpJ a b CFSG.HardMathSupport.Dickson.Sec6.Up34Th.ThThreeNative.prog3 11) =
      pkMat (RB regS) := by
    rw [Nat.eq_of_beq_eq_true hs]
    exact KernelThCent.mat_s3
  have hU : matHom17305 (slpJ a b CFSG.HardMathSupport.Dickson.I271.TabThNative.progU 22) =
      pkMat (RB regU) := by
    rw [← Nat.eq_of_beq_eq_true hu, pkMat_runPk hk _ (by decide +kernel) _ _
      (pkMat_initPk hk a b hA hB), KernelThCent.slpJ_eq]
    rfl
  obtain ⟨oZ, oS, oU, Q, hQ, hcls⟩ := census_facts (φ := matHom17305)
    (fun _ _ e => mat_injective e) ha hb hZ hS hU
  refine ⟨oS, oZ, oU, fun x hx => ?_⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hsyl : Nat.card Q = 3 ^ (Nat.card ↥J).factorization 3 := by
    rw [hQ, ThLocal.factorization_J]
  let QS : Sylow 3 ↥J := Sylow.ofCard Q hsyl
  have hxP : IsPGroup 3 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  obtain ⟨R, hR⟩ := hxP.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥J R QS
  have hmem : g * x * g⁻¹ ∈ (QS : Subgroup ↥J) := by
    have e1 := Subgroup.smul_mem_pointwise_smul x (MulAut.conj g) (R : Subgroup ↥J)
      (hR (Subgroup.mem_zpowers x))
    have e2 : ((g • R : Sylow 3 ↥J) : Subgroup ↥J) = MulAut.conj g • (R : Subgroup ↥J) := rfl
    rw [← e2, hg] at e1
    simpa [MulAut.smul_def] using e1
  have hgo : orderOf (g * x * g⁻¹) = 3 := by
    rw [← hx]
    exact orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x
  obtain ⟨k, C, hC, hkC⟩ := hcls _ (hmem : g * x * g⁻¹ ∈ Q) hgo
  have key : ∀ c : ↥J, ∀ e : ℕ, C = c ^ e → (g⁻¹ * k) * c ^ e * (g⁻¹ * k)⁻¹ = x := by
    rintro c e rfl
    have e3 : (g⁻¹ * k) * c ^ e * (g⁻¹ * k)⁻¹ = g⁻¹ * (k * c ^ e * k⁻¹) * g := by group
    rw [e3, hkC]
    group
  rcases hC with h | h | h | h | h | h
  · exact ⟨_, _, Or.inr (Or.inl rfl), 1, Or.inl rfl, key _ 1 (by rw [h, pow_one])⟩
  · exact ⟨_, _, Or.inr (Or.inl rfl), 2, Or.inr rfl, key _ 2 h⟩
  · exact ⟨_, _, Or.inl rfl, 1, Or.inl rfl, key _ 1 (by rw [h, pow_one])⟩
  · exact ⟨_, _, Or.inl rfl, 2, Or.inr rfl, key _ 2 h⟩
  · exact ⟨_, _, Or.inr (Or.inr rfl), 1, Or.inl rfl, key _ 1 (by rw [h, pow_one])⟩
  · exact ⟨_, _, Or.inr (Or.inr rfl), 2, Or.inr rfl, key _ 2 h⟩

end CertificateChecks.KernelThCensus

end
