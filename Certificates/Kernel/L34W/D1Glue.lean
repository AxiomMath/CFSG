
module

public import Certificates.Kernel.L34W.D1
public import Certificates.Kernel.L34W.TwoGlue
public import Certificates.Kernel.L34W.OuterGlue
public import CFSG.Certificates.Kernel.L34W.FixSound

public section

namespace CertificateChecks.KernelL34W

open CFSG.KC.Enum CFSG.KS CFSG.KC.L34W
open CFSG.ComponentClassification.GrSLit.L34Facts.Real CFSG.ComponentClassification.GrSLit.L34Facts.Real.WIso

theorem lt_of_kbFull : ∀ q < 15, kbFull (kbOfMask (kbMasks.getD q 0)) = false → q < 14 := by
  decide +kernel

theorem d1One_all : ∀ q < 14, d1One T1X.F AlX.F OT BT CM D1W (kbMasks.getD q 0) q = true := by
  intro q hq
  rcases (by omega : q < 5 ∨ (5 ≤ q ∧ q < 10) ∨ (10 ≤ q ∧ q < 14)) with h | h | h
  · have h1 := d1_k0
    unfold d1OK at h1
    have h2 := allN_spec h1 q h
    rwa [show Nat.add 0 q = q from Nat.zero_add q] at h2
  · have h1 := d1_k5
    unfold d1OK at h1
    have h2 := allN_spec h1 (q - 5) (by omega)
    rwa [show Nat.add 5 (q - 5) = q by change 5 + (q - 5) = q; omega] at h2
  · have h1 := d1_k10
    unfold d1OK at h1
    have h2 := allN_spec h1 (q - 10) (by omega)
    rwa [show Nat.add 10 (q - 10) = q by change 10 + (q - 10) = q; omega] at h2

theorem brow {j : ℕ} (hj : j < 144) : BRow (BT j) (OT j % 64) (OT j / 64) :=
  fun _ hk => (bt_dec hj hk).2

theorem d1_spec : ∀ kb ∈ kbList, kbFull kb = false →
    ∀ t < 64, ∀ i < 36, ∀ t' < 64, ∀ i' < 36, repInS.contains i = false →
      repInS.contains i' = false → yPerm t i * yPerm t i = 1 → yPerm t' i' * yPerm t' i' = 1 →
      yPerm t i * yPerm t' i' = yPerm t' i' * yPerm t i →
      ∃ a ∈ allM, ∃ b ∈ allM, eqKB kb b a = false ∧ fixKB kb t i a = true ∧
        fixKB kb t' i' a = true ∧ isInvKB kb a = true ∧ fixKB kb t i b = true ∧
        fixKB kb t' i' b = true ∧ isInvKB kb b = true := by
  intro kb hkb hf t ht i hi t' ht' i' hi' hS hS' h2 h2' hc
  obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hkb
  obtain ⟨q, hq, rfl⟩ := mem_kbMasks_getD m hm
  have hq14 := lt_of_kbFull q hq hf
  obtain ⟨j, hj, ej⟩ := out_mem ht hi hS h2
  obtain ⟨j', hj', ej'⟩ := out_mem ht' hi' hS' h2'
  have et : OT j % 64 = t := by omega
  have ei : OT j / 64 = i := by omega
  have et' : OT j' % 64 = t' := by omega
  have ei' : OT j' / 64 = i' := by omega
  have hcm : hasBit (CM j) j' = true := (cm_iff hj hj').2 (by rw [et, ei, et', ei']; exact hc)
  have h := d1One_all q hq14
  unfold d1One at h
  have h1 := allN_spec h j hj
  simp only [strictB_eq] at h1
  rcases bIf_iff.1 (allN_spec h1 j' hj') with ⟨-, h3⟩ | ⟨h3, -⟩
  · have r := d1W_spec t1Of alOf (brow hj) (brow hj') (by omega) (by omega) h3
    rw [et, ei, et', ei'] at r
    exact r
  · rw [hcm] at h3
    exact absurd h3 (by decide)

end CertificateChecks.KernelL34W

end
