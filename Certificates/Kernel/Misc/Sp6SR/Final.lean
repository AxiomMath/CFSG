module

public import Certificates.Kernel.Misc.Sp6SR.FactsX
public import Certificates.Kernel.Misc.Sp6SR.FactsF

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMisc.Sp6SR.Facts

open CFSG.KC.Misc.Sp6Transv CFSG.KC.Misc.Clos CFSG.KD.Sp62 CFSG.KC.Sp62 CFSG.KC.Misc.Sp6SR
open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two CFSG.Quasithin.G2U
open CFSG.RankThree.PartTwo.Sec21.FF79
open CFSG.RankThree.PartTwo.Sec21.FF81.Sp6SR CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII
open CertificateChecks.KernelMisc.Sp6SR

variable {z : Fin 3 → H6} {s : H6}

theorem Hyp.cnts (H : Hyp z s) {t : ℕ} (ht : t < 3) :
    Nat.card ↥(RSub t ⊓ Cen (z 0)) = cntT t (KY 1) ∧
      Nat.card ↥(RSub t ⊓ Cen (z 0 * (z 1 * z 2))) = cntT t (KY 6) ∧
      Nat.card ↥(RSub t ⊓ Cen (z 1 * z 2)) = cntT t (KY 4) :=
  ⟨H.card_cnt ht H.ez0, H.card_cnt ht H.ex2, H.card_cnt ht H.eu⟩

theorem Hyp.srConcl (H : Hyp z s) : SRConcl ⊤ (z 0) (z 1) (z 2) s := by
  unfold SRConcl
  rw [top_inf_eq]
  refine ⟨H.clause_i, H.clause_ii, fun R hR h2 hN hs => ?_⟩
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9⟩ := cnt_parts
  obtain ⟨r0, r1, r2, r3⟩ := ro_facts
  have hcard : ∀ t < 3, Nat.card (RSub t) = RO (t + 1) - RO t := fun t ht => (H.R_facts t ht).2.1
  rcases H.normal_cases hR h2 hN hs with rfl | rfl | rfl | rfl
  · left
    have hsq := H.s_sq
    have hc : Nat.card (Subgroup.zpowers s) = 2 := by
      rw [Nat.card_zpowers]
      exact orderOf_eq_prime (by rw [sq]; exact hsq) H.rels.2.1
    have hz : ∀ {y : H6} {b : ℕ}, enc6 y = b → MULF (KY 0) b = MULF b (KY 0) →
        Nat.card ↥(Subgroup.zpowers s ⊓ Cen y) = 2 := by
      intro y b ey e
      rw [inf_eq_left.mpr (Subgroup.zpowers_le.mpr (mem_cen_of H.es ey e)), hc]
    exact ⟨hc, hz H.ez0 (by decide +kernel), hz H.ex2 (by decide +kernel),
      hz H.eu (by decide +kernel)⟩
  · obtain ⟨e1, e2, e3⟩ := H.cnts (t := 0) (by norm_num)
    refine Or.inr (Or.inl ⟨?_, ?_, ?_, ?_, H.clause_8⟩)
    · rw [hcard 0 (by norm_num), r1, r0]
    · rw [e1, c1]
    · rw [e2, c2]
    · rw [e3, c3]
  · obtain ⟨e1, e2, e3⟩ := H.cnts (t := 1) (by norm_num)
    refine Or.inr (Or.inr (Or.inl ⟨?_, ?_, ?_, ?_, H.clause_32⟩))
    · rw [hcard 1 (by norm_num), r2, r1]
    · rw [e1, c4]
    · rw [e2, c5]
    · rw [e3, c6]
  · obtain ⟨e1, e2, e3⟩ := H.cnts (t := 2) (by norm_num)
    obtain ⟨f1, f2, f3⟩ := H.r3_cenS_facts
    obtain ⟨x1, x2, x3, x4, x5⟩ := H.x_facts
    refine Or.inr (Or.inr (Or.inr ⟨?_, ?_, ?_, ?_, H.r3_z0_elemAb, f1, f2, f3, ?_⟩))
    · rw [hcard 2 (by norm_num), r3, r2]
    · rw [e1, c7]
    · rw [e2, c8]
    · rw [e3, c9]
    · rw [H.sup_eq_X]
      exact ⟨x1, x2, x3, x4, x5⟩

theorem sp6SRFacts_kernel : Sp6SRFacts := by
  unfold Sp6SRFacts
  refine ⟨⟨ofCode (srC, srC) (pairCheck_of (by decide +kernel)), mat6_ofCode _ _⟩, ?_⟩
  intro z s hz hs
  have H : Hyp z s := ⟨hz, hs⟩
  exact ⟨H.rels, H.card_cen, H.srConcl, fun R hR h2 hN => H.card_le hR h2 hN, H.filt⟩

end CertificateChecks.KernelMisc.Sp6SR.Facts

end
