
module

public import Certificates.Kernel.L34W.Types
public import Certificates.Kernel.L34W.DGlue
public import CFSG.Certificates.Kernel.L34W.TypesSound

public section

namespace CertificateChecks.KernelL34W

open CFSG.KC.Enum CFSG.KS CFSG.KC.L34W
open CFSG.ComponentClassification.GrSLit.L34Facts CFSG.ComponentClassification.GrSLit.L34Facts.Real
open CFSG.ComponentClassification.GrSLit.L34Facts.Real.WIso

theorem kc_range {lo n : ℕ} (h : kcR kbMasks lo n = true) {m : ℕ} (hlo : lo ≤ m)
    (hm : m < lo + n) (hs : isSubM m = true) : inL kbMasks m = true := by
  unfold kcR at h
  have h1 := allN_spec h (m - lo) (by omega)
  have e : Nat.add lo (m - lo) = m := by
    change lo + (m - lo) = m
    omega
  rw [strictB_eq, e, hs] at h1
  exact h1

theorem kc_all : ∀ m < 65536, isSubM m = true → inL kbMasks m = true := by
  intro m hm hs
  rcases (by omega : m < 16384 ∨ (16384 ≤ m ∧ m < 32768) ∨ (32768 ≤ m ∧ m < 49152) ∨
      49152 ≤ m) with h | h | h | h
  · exact kc_range kc_k0 (Nat.zero_le m) (by omega) hs
  · exact kc_range kc_k1 h.1 (by omega) hs
  · exact kc_range kc_k2 h.1 (by omega) hs
  · exact kc_range kc_k3 h (by omega) hs

theorem kclass_spec (K : AddSubgroup (ZMod 4 × ZMod 4)) :
    ∃ kb ∈ kbList, ∀ i j : ZMod 4, inKB kb i j = true ↔ (i, j) ∈ K :=
  kClass_of kc_all K

theorem types_spec {t i : ℕ} (h : typeOf t i < 3) : t < 64 ∧ i < 36 ∧
    ∃ t' < 64, ∃ j < 36, yPerm t' j * yPerm t i * (yPerm t' j)⁻¹ = rhoPerm (typeOf t i) := by
  obtain ⟨e, he, e1, e2⟩ := entry_of_typeOf h
  obtain ⟨ht, hi, -, ht', hj, hc⟩ := cj_spec gensG y_k cj_k e he
  rw [e1] at ht hi hc
  rw [e2] at hc
  exact ⟨ht, hi, _, ht', _, hj, hc⟩

theorem outer_spec {t i : ℕ} (ht : t < 64) (hi : i < 36) (hS : repInS.contains i = false)
    (h2 : yPerm t i * yPerm t i = 1) : typeOf t i < 3 := by
  obtain ⟨j, hj, ej⟩ := out_mem ht hi hS h2
  have et : OT j % 64 = t := by omega
  have ei : OT j / 64 = i := by omega
  have h := ty_eq hj
  rw [et, ei] at h
  rw [h]
  exact Nat.blt_eq.mp (allN_spec to_k j hj)

theorem pairs_spec {t i t' i' : ℕ} (ht : t < 64) (hi : i < 36) (ht' : t' < 64) (hi' : i' < 36)
    (hS : repInS.contains i = false) (hS' : repInS.contains i' = false)
    (h2 : yPerm t i * yPerm t i = 1) (h2' : yPerm t' i' * yPerm t' i' = 1)
    (hc : yPerm t i * yPerm t' i' = yPerm t' i' * yPerm t i)
    (hn : yPerm t i * yPerm t' i' ∉ CFSG.ComponentClassification.PSL3Four.S) :
    typeOf t i ≠ typeOf t' i' := by
  obtain ⟨j, hj, ej⟩ := out_mem ht hi hS h2
  obtain ⟨j', hj', ej'⟩ := out_mem ht' hi' hS' h2'
  have et : OT j % 64 = t := by omega
  have ei : OT j / 64 = i := by omega
  have et' : OT j' % 64 = t' := by omega
  have ei' : OT j' / 64 = i' := by omega
  have hcm : hasBit (CM j) j' = true := (cm_iff hj hj').2 (by rw [et, ei, et', ei']; exact hc)
  have h := allN_spec tp_k j hj
  simp only [strictB_eq] at h
  rcases bIf_iff.1 (allN_spec h j' hj') with ⟨-, h3⟩ | ⟨h3, -⟩
  · rcases bIf_iff.1 h3 with ⟨h4, -⟩ | ⟨-, h4⟩
    · have e : i = i' := by
        have := Nat.eq_of_beq_eq_true h4
        change OT j / 64 = OT j' / 64 at this
        omega
      subst e
      exact absurd (mul_mem_S h2) hn
    · have hne : TY j ≠ TY j' := Nat.ne_of_beq_eq_false (bNot_iff.1 h4)
      have e1 := ty_eq hj
      have e2 := ty_eq hj'
      rw [et, ei] at e1
      rw [et', ei'] at e2
      rw [e1, e2]
      exact hne
  · rw [hcm] at h3
    exact absurd h3 (by decide)

theorem fieldSq_spec {t i : ℕ} (ht : t < 64) (hi : i < 36) (hS : repInS.contains i = false)
    (h2 : yPerm t i * yPerm t i = 1) (h0 : typeOf t i = 0) :
    ∀ z ∈ zInvs, fixKB (kbOfMask 1) t i z = true →
      ∃ x ∈ allM, fixKB (kbOfMask 1) t i x = true ∧ eqKB (kbOfMask 1) (mulM x x) z = true := by
  obtain ⟨j, hj, ej⟩ := out_mem ht hi hS h2
  have et : OT j % 64 = t := by omega
  have ei : OT j / 64 = i := by omega
  have hty : TY j = 0 := by
    have h := ty_eq hj
    rw [et, ei, h0] at h
    exact h.symm
  have hb : BRow (BT j) t i := by
    have h := brow hj
    rw [et, ei] at h
    exact h
  have h := allN_spec fs_k j hj
  rcases bIf_iff.1 h with ⟨-, h1⟩ | ⟨h1, -⟩
  · simp only [strictB_eq] at h1
    change bAnd(fsZ T1X.F AlX.F (BT j) (OT j / 64) 8, bAnd(fsZ T1X.F AlX.F (BT j) (OT j / 64) 2,
      fsZ T1X.F AlX.F (BT j) (OT j / 64) 10)) = true at h1
    rw [ei, bAnd_iff, bAnd_iff] at h1
    obtain ⟨f8, f2, f10⟩ := h1
    intro z hz hf
    simp only [zInvs, List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl
    · have e : ((0, 2, 0) : MElt) = dec 8 := by decide
      rw [e] at hf ⊢
      exact fsZ_spec t1Of alOf hb hi (by norm_num) f8 hf
    · have e : ((0, 0, 2) : MElt) = dec 2 := by decide
      rw [e] at hf ⊢
      exact fsZ_spec t1Of alOf hb hi (by norm_num) f2 hf
    · have e : ((0, 2, 2) : MElt) = dec 10 := by decide
      rw [e] at hf ⊢
      exact fsZ_spec t1Of alOf hb hi (by norm_num) f10 hf
  · rw [hty] at h1
    exact absurd h1 (by decide)

end CertificateChecks.KernelL34W

end
