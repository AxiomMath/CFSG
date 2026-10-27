module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThCentSound
public import CFSG.Open.LocalVocabulary
public import Certificates.Certificate1020
public import Certificates.Certificate1021
public import Certificates.Certificate1022
import Certificates.Kernel.ThLocal.Facts
import Certificates.Kernel.ThCensus.Pin
import Certificates.Kernel.ThCent.Consumers
import CFSG.Certificates.Kernel.ThCent.PinSound
import CFSG.Certificates.Kernel.Th.Spec.DceMat
import CFSG.Sporadic.Th.Max3.AllConjFinal
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThCentSoundBase2
public import CFSG.Sporadic.Th.CertificateBase
public import CFSG.Sporadic.ThSchreier.KernelAut
public import CFSG.Sporadic.ThSchreier.KernelAutBase
public import CFSG.Sporadic.ThSchreier.KernelAutBase1

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelThLocal

open CFSG.Sporadic.Th CFSG.KC.Th CFSG.KC.ThCent CFSG.KC.Th.Spec CFSG.KC.Th.Spec.FwdRel
  CFSG.KD.ThCensus CFSG.HardMathSupport.Timmesfeld.SporadicBalance CertificateChecks.KernelThCensus


@[expose] noncomputable def matHom13650 : ↥J →* Matrix (Fin 248) (Fin 248) (ZMod 2) :=
  (Units.coeHom (Matrix (Fin 248) (Fin 248) (ZMod 2))).comp J.subtype

theorem th_local13650 :
    ∃ Q : Subgroup ↥J, Nat.card Q = 3 ^ 10 ∧ ThCent.zJ ∈ Q ∧ ThCent.zJ ^ 3 = 1 ∧
      (∀ q ∈ Q, q * ThCent.zJ = ThCent.zJ * q) ∧
      (∃ u : ↥J, orderOf u = 2 ∧ u * ThCent.zJ = ThCent.zJ * u) ∧
      ∀ s ∈ Q, orderOf s = 3 → ∃ t : ↥J, IsConj s t ∧
        3 ^ 7 ≤ Nat.card ↥(Q ⊓ Subgroup.centralizer ({t} : Set ↥J)) ∧
        ∃ E : Subgroup ↥J, E ≤ Subgroup.centralizer ({t} : Set ↥J) ∧
          CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 9 ∧
          ∀ x ∈ E, x ≠ 1 → IsConj x ThCent.zJ ∨ IsConj x (ThCent.zJ ^ 2) := by
  have hfin : Finite ↥J :=
    Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Th.Max3.natCard_J]; norm_num)
  obtain ⟨hA, hB, -, -⟩ := KernelThCent.fwd_mats
  obtain ⟨h1, hJ⟩ := Dce.andB_iff.1 ch17305J
  obtain ⟨h2, hJ⟩ := Dce.andB_iff.1 hJ
  obtain ⟨hz, -⟩ := Dce.andB_iff.1 hJ
  have ha : matHom13650 a = pkMat (RB 1) := by
    rw [Nat.eq_of_beq_eq_true h1]
    exact hA
  have hb : matHom13650 b = pkMat (RB 2) := by
    rw [Nat.eq_of_beq_eq_true h2]
    exact hB
  have hZ : matHom13650 ThCent.zJ = pkMat (RB regZ) := by
    rw [Nat.eq_of_beq_eq_true hz]
    exact KernelThCent.mat_zJ
  exact local_facts (φ := matHom13650) (fun _ _ e => mat_injective e) ha hb hZ

end CertificateChecks.KernelThLocal

end
