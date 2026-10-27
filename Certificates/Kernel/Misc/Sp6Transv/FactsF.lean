module

public import Certificates.Kernel.Misc.Sp6Transv.FactsN
import Certificates.Kernel.Sp62.Final
import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIIISp62Check

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMisc.Sp6Transv.Facts

open CFSG.KC.Misc.Sp6Transv CFSG.KC.Misc.Clos CFSG.KD.Sp62 CFSG.KC.Sp62
open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two CFSG.Quasithin.G2U
open CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Transv CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII
open CertificateChecks.KernelMisc.Sp6Transv

variable {z : Fin 3 → H6} {t s f0 f2 : H6} {q : Fin 5 → H6}

theorem filt_all : ∀ i < 2160, filtAt REC (KS 0) (KS 2) (MULF (KS 2) (KS 2)) (KS 3)
    (MULF (MULF (KS 2) (KS 0)) (MULF (KS 2) (KS 2))) (MULF (MULF (MULF (KS 2) (KS 2)) (KS 0)) (KS 2))
      i = true := by
  have h := forall_of_chunks 540 4 _ (fun c hc => by
    have e := FK.all c hc
    unfold fB at e
    rw [letB_eq] at e
    exact e)
  exact fun i hi => h i (by omega)

theorem Hyp.code_C (H : Hyp z t s f0 f2 q) {x : H6}
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

theorem Hyp.filt (H : Hyp z t s f0 f2 q) : ∀ x : H6, x * z 0 = z 0 * x → x * z 2 = z 2 * x →
    x * x = 1 → x ≠ 1 → x * z 1 * x⁻¹ = (z 1)⁻¹ →
      x = s ∨ x = z 1 * s * (z 1)⁻¹ ∨ x = (z 1)⁻¹ * s * z 1 := by
  intro x h0 h2 hsq h1 hz1
  have hx0 : x ∈ Subgroup.centralizer ({z 0} : Set H6) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    first | exact h0 | exact h0.symm
  obtain ⟨i, hi, ei⟩ := H.code_C hx0
  have hf := filt_all i hi
  unfold filtAt at hf
  rw [letB_eq, ← ei] at hf
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hsq
  have c1 : commF (enc6 x) (KS 3) = true := by
    rw [← H.ez2, commF_iff, Subgroup.mem_centralizer_singleton_iff]
    first | exact h2 | exact h2.symm
  have c2 : Nat.beq (MULF (enc6 x) (enc6 x)) ONE = true := by
    rw [← emul, hsq, enc_one]
    exact Nat.beq_refl _
  have c3 : Nat.beq (enc6 x) ONE = false := by
    cases hb : Nat.beq (enc6 x) ONE
    · rfl
    · exact absurd (eq_of_enc (by rw [enc_one]; exact Nat.eq_of_beq_eq_true hb)) h1
  have c4 : Nat.beq (MULF (MULF (enc6 x) (KS 2)) (enc6 x)) (MULF (KS 2) (KS 2)) = true := by
    rw [← H.ez1, ← emul, ← emul, ← emul]
    rw [hxi] at hz1
    rw [hz1, H.z_inv1]
    exact Nat.beq_refl _
  rw [c1, c2, c3, c4] at hf
  have hf' := orB_true hf
  rcases hf' with hf' | hf'
  · exact absurd hf' (by decide)
  rcases orB_true hf' with e | e
  · exact Or.inl (eq_of_enc (by rw [H.es]; exact Nat.eq_of_beq_eq_true e))
  rcases orB_true e with e | e
  · refine Or.inr (Or.inl (eq_of_enc ?_))
    rw [H.z_inv1, emul, emul, emul, H.es, H.ez1]
    exact Nat.eq_of_beq_eq_true e
  · refine Or.inr (Or.inr (eq_of_enc ?_))
    rw [H.z_inv1, emul, emul, emul, H.es, H.ez1]
    exact Nat.eq_of_beq_eq_true e

end CertificateChecks.KernelMisc.Sp6Transv.Facts

end
