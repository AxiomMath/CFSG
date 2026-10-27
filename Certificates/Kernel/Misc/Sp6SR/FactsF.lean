module

public import Certificates.Kernel.Misc.Sp6SR.Facts
import Certificates.Kernel.Sp62.Final
import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIIISp62Check

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMisc.Sp6SR.Facts

open CFSG.KC.Misc.Sp6Transv CFSG.KC.Misc.Clos CFSG.KD.Sp62 CFSG.KC.Sp62 CFSG.KC.Misc.Sp6SR
open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two CFSG.Quasithin.G2U
open CFSG.RankThree.PartTwo.Sec21.FF81.Sp6SR CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII
open CertificateChecks.KernelMisc.Sp6SR
open CertificateChecks.KernelMisc.Sp6Transv.Facts (orB_true commF_iff)

variable {z : Fin 3 → H6} {s : H6}

theorem filt_all : ∀ i < 2160, filtAt REC (KY 0) (KY 5) (KY 8) (KY 4)
    (MULF (MULF (KY 5) (KY 0)) (KY 8)) (MULF (MULF (KY 8) (KY 0)) (KY 5)) i = true := by
  have h := forall_of_chunks 540 4 _ (fun c hc => chF.all c hc)
  exact fun i hi => h i (by omega)

theorem Hyp.code_C (H : Hyp z s) {x : H6}
    (hx : x ∈ Subgroup.centralizer ({z 0} : Set H6)) : ∃ i < 2160, enc6 x = recX REC 38 i := by
  have hz : z 0 = aElt 0 := by
    refine eq_of_enc ?_
    rw [H.ez0, aElt, enc6_of (mat6_vecElt _) (a_ok 0).1, (a_ok 0).2]
    decide +kernel
  rw [hz, ← centSub_eq] at hx
  have hok := (clos_ok 0).1
  obtain ⟨i, hi, e, hc⟩ := exists_code_closure (centGens 0) (pairs_spec.2.2.2 0) _ hok hx
  have hsz := hok
  simp only [closureOK, Bool.and_eq_true, beq_iff_eq] at hsz
  have hi' : i < 2160 := by
    have := hsz.1.1.1
    change i < (closureT (gs 0)).size at hi
    rw [this] at hi
    exact hi
  refine ⟨i, hi', ?_⟩
  rw [enc6_of e.symm hc]
  exact ((clos_ok 0).2 i hi').2

theorem Hyp.filt (H : Hyp z s) : ∀ x : H6, x * z 0 = z 0 * x →
    x * (z 1 * z 2) = z 1 * z 2 * x → x * x = 1 → x ≠ 1 →
    x * (z 1 * z 2 ^ 2) * x⁻¹ = (z 1 * z 2 ^ 2)⁻¹ →
      x = s ∨ x = z 1 * z 2 ^ 2 * s * (z 1 * z 2 ^ 2)⁻¹ ∨
        x = (z 1 * z 2 ^ 2)⁻¹ * s * (z 1 * z 2 ^ 2) := by
  intro x h0 hu hsq h1 hw
  have hx0 : x ∈ Subgroup.centralizer ({z 0} : Set H6) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    first | exact h0 | exact h0.symm
  obtain ⟨i, hi, ei⟩ := H.code_C hx0
  have hf := filt_all i hi
  unfold filtAt at hf
  rw [letB_eq, ← ei] at hf
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hsq
  have c1 : commF (enc6 x) (KY 4) = true := by
    rw [← H.eu, commF_iff, Subgroup.mem_centralizer_singleton_iff]
    first | exact hu | exact hu.symm
  have c2 : Nat.beq (MULF (enc6 x) (enc6 x)) ONE = true := by
    rw [← emul, hsq, enc_one]
    exact Nat.beq_refl _
  have c3 : Nat.beq (enc6 x) ONE = false := by
    cases hb : Nat.beq (enc6 x) ONE
    · rfl
    · exact absurd (eq_of_enc (by rw [enc_one]; exact Nat.eq_of_beq_eq_true hb)) h1
  have c4 : Nat.beq (MULF (MULF (enc6 x) (KY 5)) (enc6 x)) (KY 8) = true := by
    rw [← H.ew, ← H.ew2, ← emul, ← emul]
    rw [hxi] at hw
    rw [hw, H.w_inv]
    exact Nat.beq_refl _
  have ea1 : enc6 (z 1 * z 2 ^ 2 * s * (z 1 * z 2 ^ 2)⁻¹) = MULF (MULF (KY 5) (KY 0)) (KY 8) := by
    rw [H.w_inv, emul (z 1 * z 2 ^ 2 * s), emul (z 1 * z 2 ^ 2) s, H.ew, H.es, H.ew2]
  have ea2 : enc6 ((z 1 * z 2 ^ 2)⁻¹ * s * (z 1 * z 2 ^ 2)) = MULF (MULF (KY 8) (KY 0)) (KY 5) := by
    rw [H.w_inv, emul (z 1 * z 2 ^ 2 * (z 1 * z 2 ^ 2) * s),
      emul (z 1 * z 2 ^ 2 * (z 1 * z 2 ^ 2)) s, H.ew2, H.es, H.ew]
  rw [c1, c2, c3, c4] at hf
  rcases orB_true hf with hf' | hf'
  · exact absurd hf' (by decide)
  rcases orB_true hf' with e | e
  · exact Or.inl (eq_of_enc (by rw [H.es]; exact Nat.eq_of_beq_eq_true e))
  rcases orB_true e with e | e
  · exact Or.inr (Or.inl (eq_of_enc ((Nat.eq_of_beq_eq_true e).trans ea1.symm)))
  · exact Or.inr (Or.inr (eq_of_enc ((Nat.eq_of_beq_eq_true e).trans ea2.symm)))

end CertificateChecks.KernelMisc.Sp6SR.Facts

end
