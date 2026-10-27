
module

public import Certificates.Kernel.L34W.D
public import Certificates.Kernel.L34W.D1Glue

public section

namespace CertificateChecks.KernelL34W

open CFSG.KC.Enum CFSG.KS CFSG.KC.L34W
open CFSG.ComponentClassification.GrSLit.L34Facts.Real CFSG.ComponentClassification.GrSLit.L34Facts.Real.WIso

theorem dOne_all : ∀ q < 15, dOne T1X.F AlX.F OT BT LF TY DW (kbMasks.getD q 0) q = true := by
  intro q hq
  rcases (by omega : q < 5 ∨ (5 ≤ q ∧ q < 10) ∨ (10 ≤ q ∧ q < 15)) with h | h | h
  · have h1 := d_k0
    unfold dOK at h1
    have h2 := allN_spec h1 q h
    rwa [show Nat.add 0 q = q from Nat.zero_add q] at h2
  · have h1 := d_k5
    unfold dOK at h1
    have h2 := allN_spec h1 (q - 5) (by omega)
    rwa [show Nat.add 5 (q - 5) = q by change 5 + (q - 5) = q; omega] at h2
  · have h1 := d_k10
    unfold dOK at h1
    have h2 := allN_spec h1 (q - 10) (by omega)
    rwa [show Nat.add 10 (q - 10) = q by change 10 + (q - 10) = q; omega] at h2

theorem lf_bit {q i : ℕ} (hq : q < 15) (hi : i < 36)
    (hl : liftsKB (kbOfMask (kbMasks.getD q 0)) i = true) : hasBit (LF q) i = true := by
  have h := lf_k
  unfold lfOK at h
  rw [liftsKB_eq alOf _ hi] at hl
  rcases bIf_iff.1 (allN_spec (allN_spec h q hq) i hi) with ⟨-, h1⟩ | ⟨h1, -⟩
  · exact h1
  · exact absurd (hl.symm.trans h1) (by decide)

theorem ty_eq {j : ℕ} (hj : j < 144) : typeOf (OT j % 64) (OT j / 64) = TY j := by
  exact Nat.eq_of_beq_eq_true (allN_spec ty_k j hj)

theorem d_spec : ∀ kb ∈ kbList, ∀ t < 64, ∀ i < 36, repInS.contains i = false →
    yPerm t i * yPerm t i = 1 → liftsKB kb i = true → ∀ k < 64,
    (k = 0 ∨ ((mulM (k, 0, 0) (k, 0, 0)).1 = 0 ∧ (betaYM t i (k, 0, 0)).1 = k)) →
    (∃ x, DProp kb t i k x ∧ x.1 ≠ 0 ∧ x.1 ≠ k) ∨
      (∃ a b c d, DProp kb t i k a ∧ DProp kb t i k b ∧ DProp kb t i k c ∧ DProp kb t i k d ∧
        eqKB kb b a = false ∧ eqKB kb c a = false ∧ eqKB kb c b = false ∧
        eqKB kb d a = false ∧ eqKB kb d b = false ∧ eqKB kb d c = false) ∨
      (k ≠ 0 ∧ typeOf t i = expType kb ∧ (kbZero kb = true ∨ kbCyc kb = true) ∧
        (kbFull kb = true ∨ ∃ a b c, DProp kb t i k a ∧ DProp kb t i k b ∧ DProp kb t i k c ∧
          eqKB kb b a = false ∧ eqKB kb c a = false ∧ eqKB kb c b = false)) := by
  intro kb hkb t ht i hi hS h2 hl k hk hkv
  obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hkb
  obtain ⟨q, hq, rfl⟩ := mem_kbMasks_getD m hm
  obtain ⟨j, hj, ej⟩ := out_mem ht hi hS h2
  have et : OT j % 64 = t := by omega
  have ei : OT j / 64 = i := by omega
  have hlf := lf_bit hq hi hl
  have hkv' : kvK T1X.F BT j k = true := (kv_iff' hj hk).2 (by rw [et, ei]; exact hkv)
  have h := dOne_all q hq
  unfold dOne at h
  simp only [strictB_eq] at h
  rcases bIf_iff.1 (allN_spec h j hj) with ⟨-, h1⟩ | ⟨h1, -⟩
  · rcases bIf_iff.1 (allN_spec h1 k hk) with ⟨-, h3⟩ | ⟨h3, -⟩
    · have r := dW_spec t1Of alOf (brow hj) (by omega) hk hq (ty_eq hj) h3
      rw [et, ei] at r
      exact r
    · rw [hkv'] at h3
      exact absurd h3 (by decide)
  · have e : OT j / 64 = (OT j).div 64 := rfl
    rw [← e, ei, hlf] at h1
    exact absurd h1 (by decide)

end CertificateChecks.KernelL34W

end
