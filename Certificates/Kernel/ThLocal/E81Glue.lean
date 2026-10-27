module

public import CFSG.Sporadic.Th.Setup
public import CFSG.Open.LocalVocabulary
public import Certificates.Certificate1020
public import Certificates.Certificate1021
public import Certificates.Certificate1022
import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThCentSound
import Certificates.Kernel.ThLocal.E81Facts
import Certificates.Kernel.ThLocal.Glue
import Certificates.Kernel.ThCensus.Pin
import Certificates.Kernel.ThCent.Consumers
import CFSG.Certificates.Kernel.ThCent.PinSound
import CFSG.Certificates.Kernel.Th.Spec.DceMat
import CFSG.Sporadic.Th.Max3.AllConjFinal
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelThLocal

open CFSG.Sporadic.Th CFSG.KC.Th CFSG.KC.ThCent CFSG.KC.Th.Spec CFSG.KC.Th.Spec.FwdRel
  CFSG.KD.ThCensus CFSG.HardMathSupport.Timmesfeld.SporadicBalance CertificateChecks.KernelThCensus

theorem cover_map {W : Type*} [Group W] (K : Subgroup W) {Z : ↥K}
    (h : ∃ Q : Subgroup ↥K, Nat.card Q = 3 ^ 10 ∧ Z ∈ Q ∧ Z ^ 3 = 1 ∧ Z ≠ 1 ∧
      (∀ q ∈ Q, q * Z = Z * q) ∧
      ∀ s ∈ Q, s ^ 3 = 1 → s ∉ Subgroup.zpowers Z →
        ∃ E : Subgroup ↥K, E ≤ Q ∧ CFSG.Open.IsElemAbelian 3 E ∧ 81 ≤ Nat.card E ∧ s ∈ E ∧
          Z ∈ E) :
    ∃ (Q : Subgroup W) (z : W), Q ≤ K ∧ Nat.card Q = 3 ^ 10 ∧ z ^ 3 = 1 ∧ z ≠ 1 ∧ z ∈ Q ∧
      (∀ q ∈ Q, q * z = z * q) ∧
      ∀ s ∈ Q, s ^ 3 = 1 → s ∉ Subgroup.zpowers z →
        ∃ E : Subgroup W, E ≤ Q ∧ CFSG.Open.IsElemAbelian 3 E ∧ 81 ≤ Nat.card E ∧ s ∈ E ∧
          z ∈ E := by
  obtain ⟨Q, hQ, hzQ, hz3, hz1, hzc, hcov⟩ := h
  have hinj : Function.Injective K.subtype := Subtype.val_injective
  refine ⟨Q.map K.subtype, K.subtype Z, Subgroup.map_subtype_le Q, ?_, ?_, ?_,
    Subgroup.mem_map_of_mem _ hzQ, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective hinj, hQ]
  · rw [← map_pow, hz3, map_one]
  · intro e
    apply hz1
    apply hinj
    rw [e, map_one]
  · rintro _ ⟨q, hq, rfl⟩
    rw [← map_mul, ← map_mul, hzc q hq]
  · rintro _ ⟨s, hs, rfl⟩ hs3 hsz
    have hs3' : s ^ 3 = 1 := by
      apply hinj
      rw [map_pow, hs3, map_one]
    have hsz' : s ∉ Subgroup.zpowers Z := by
      intro hm
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hm
      apply hsz
      refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
      rw [← map_zpow, hk]
    obtain ⟨E, hEQ, hE, hE81, hsE, hzE⟩ := hcov s hs hs3' hsz'
    refine ⟨E.map K.subtype, Subgroup.map_mono hEQ, CFSG.Open.IsElemAbelian.map hE _, ?_,
      Subgroup.mem_map_of_mem _ hsE, Subgroup.mem_map_of_mem _ hzE⟩
    rw [Subgroup.card_map_of_injective hinj]
    exact hE81


theorem th_e81_9521 :
    ∃ (Q : Subgroup (GL (Fin 248) (ZMod 2))) (z : GL (Fin 248) (ZMod 2)), Q ≤ J ∧
      Nat.card Q = 3 ^ 10 ∧ z ^ 3 = 1 ∧ z ≠ 1 ∧ z ∈ Q ∧ (∀ q ∈ Q, q * z = z * q) ∧
      ∀ s ∈ Q, s ^ 3 = 1 → s ∉ Subgroup.zpowers z →
        ∃ E : Subgroup (GL (Fin 248) (ZMod 2)), E ≤ Q ∧ CFSG.Open.IsElemAbelian 3 E ∧
          81 ≤ Nat.card E ∧ s ∈ E ∧ z ∈ E := by
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
  obtain ⟨Q, hQ, hzQ, hz3, hz1, hzc, hcov⟩ :=
    e81_facts (φ := matHom13650) (fun _ _ e => mat_injective e) ha hb hZ
  exact cover_map J ⟨Q, hQ, hzQ, hz3, hz1, hzc, hcov⟩

end CertificateChecks.KernelThLocal

end
