module

public import Certificates.Kernel.Sporadic.Fi22.Pair214032K
public import Certificates.Kernel.Sporadic.Fi22.Pump36908G

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Pair214032

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Fi22Pump CFSG.KC.PtOrb CFSG.KC.BfsPin
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.Fv8124
open CertificateChecks.KernelSpor.Pump36908
open CFSG.Monster.B.Fischer CFSG.RankThree.Native
open CertificateChecks.KernelFi22Reps (xT rep_xT)
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi22Three (xRep)

theorem zY' {j : ℕ} (hj : j < 2) : chkY S (Fi22X.inv S) (xT 3) (Z j) = true := by
  have h := zY
  simp only [Fv8124.strictB_eq] at h
  exact allN_spec' h hj

theorem pZ {j : ℕ} (hj : j < 2) : PP 3510 12 (Z j) := by
  have h := zY' hj
  unfold chkY at h
  simp only [Bool.and_eq_true] at h
  exact PP_of_isP h.1.1.1.1

theorem z_facts {j : ℕ} (hj : j < 2) :
    pe (Z j) ∈ fi22P ∧ orderOf (pe (Z j)) = 5 ∧
      pe (Z j) * (pe S * MulAction.toPerm (xRep 3) * (pe S)⁻¹) =
        pe S * MulAction.toPerm (xRep 3) * (pe S)⁻¹ * pe (Z j) := by
  have h := zY' hj
  unfold chkY at h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨hp, hs⟩, h5⟩, h1⟩, hc⟩ := h
  have pY := PP_of_isP hp
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  refine ⟨(mem_P pY).2 hs, orderOf_eq_prime ?_ ?_, ?_⟩
  · rw [← pe_pw pY, ← pe_id]
    exact (pe_eq_iff (PP_pw pY 5) PP_id).2 h5
  · rw [← pe_id]
    exact ne_of pY PP_id h1
  · have hT := rep_xT (k := 3) (by norm_num)
    refine ext_val fun v => ?_
    rw [app2 (pe (Z j)), app2 _ (pe (Z j)), pe_apply pY, X_apply pS hT, X_apply pS hT,
      pe_apply pY]
    exact commC_spec hc v.2

theorem orbit_dvd (G : Subgroup (Equiv.Perm (Fin 3510))) (x : Fin 3510) :
    Nat.card (MulAction.orbit G x) ∣ Nat.card G := by
  rw [Nat.card_coe_set_eq, ← MulAction.index_stabilizer]
  exact Subgroup.index_dvd_card _

theorem dvd_pair :
    405 ∣ Nat.card (Subgroup.closure ({pe (Z 0), pe (Z 1)} : Set (Equiv.Perm (Fin 3510)))) := by
  have h := zO
  simp only [Fv8124.strictB_eq] at h
  obtain ⟨hc, hpop⟩ := orbC_spec h
  have e := (card_orbit (gens_eq (pe (Z 0)) (pe (Z 1)))
    (gY_eq (fun x => (pe_apply (pZ (j := 0) (by norm_num)) x).symm)
      (fun x => (pe_apply (pZ (j := 1) (by norm_num)) x).symm)) (by norm_num : 1 < 3510) hc).trans
    hpop
  rw [← e]
  exact orbit_dvd _ _

theorem facts214032 :
    ∃ σ : Equiv.Perm (Fin 3510),
      (∀ v : Fin 3510,
        (CFSG.HardMathSupport.Solomon.Coordinator.Fi22Pump.sigmaArr ())[(v : ℕ)]! = σ v) ∧
      ∃ Y₁ Y₂ : Equiv.Perm (Fin 3510), Y₁ ∈ fi22P ∧ Y₂ ∈ fi22P ∧ orderOf Y₁ = 5 ∧
        orderOf Y₂ = 5 ∧
        Y₁ * (σ * MulAction.toPerm (xRep 3) * σ⁻¹) = σ * MulAction.toPerm (xRep 3) * σ⁻¹ * Y₁ ∧
        Y₂ * (σ * MulAction.toPerm (xRep 3) * σ⁻¹) = σ * MulAction.toPerm (xRep 3) * σ⁻¹ * Y₂ ∧
        405 ∣ Nat.card (Subgroup.closure ({Y₁, Y₂} : Set (Equiv.Perm (Fin 3510)))) := by
  obtain ⟨m0, o0, c0⟩ := z_facts (j := 0) (by norm_num)
  obtain ⟨m1, o1, c1⟩ := z_facts (j := 1) (by norm_num)
  exact ⟨pe S, rep_sigma, pe (Z 0), pe (Z 1), m0, m1, o0, o1, c0, c1, dvd_pair⟩

end CertificateChecks.KernelSpor.Pair214032

end
