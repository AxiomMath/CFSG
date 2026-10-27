module

public import Certificates.Kernel.Misc.Sp6Transv.FactsF
public import Certificates.Kernel.Misc.Sp6Transv.FactsW

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMisc.Sp6Transv.Facts

open CFSG.KC.Misc.Sp6Transv CFSG.KC.Misc.Clos CFSG.KD.Sp62 CFSG.KC.Sp62
open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two CFSG.Quasithin.G2U
open CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Transv CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII
open CertificateChecks.KernelMisc.Sp6Transv

variable {z : Fin 3 → H6} {t s f0 f2 : H6} {q : Fin 5 → H6}

theorem welt_eq (z : Fin 3 → H6) (t : H6) {a b c j : ℕ} (ha : a < 3) (hb : b < 3) (hc : c < 3)
    (hj : j < 3) : welt z t (27 * a + 9 * b + 3 * c + j) = z 0 ^ a * z 1 ^ b * z 2 ^ c * t ^ j := by
  have e1 : Nat.div (27 * a + 9 * b + 3 * c + j) 27 = a := by
    change (27 * a + 9 * b + 3 * c + j) / 27 = a
    omega
  have e2 : Nat.mod (Nat.div (27 * a + 9 * b + 3 * c + j) 9) 3 = b := by
    change (27 * a + 9 * b + 3 * c + j) / 9 % 3 = b
    omega
  have e3 : Nat.mod (Nat.div (27 * a + 9 * b + 3 * c + j) 3) 3 = c := by
    change (27 * a + 9 * b + 3 * c + j) / 3 % 3 = c
    omega
  have e4 : Nat.mod (27 * a + 9 * b + 3 * c + j) 3 = j := by
    change (27 * a + 9 * b + 3 * c + j) % 3 = j
    omega
  rw [welt, e1, e2, e3, e4]

theorem Hyp.syl (H : Hyp z t s f0 f2 q) : ∀ a < 3, ∀ b < 3, ∀ c < 3, ∀ j < 3,
    (z 0 ^ a * z 1 ^ b * z 2 ^ c * t ^ j) ^ 3 = 1 → z 0 ^ a * z 1 ^ b * z 2 ^ c * t ^ j ≠ 1 →
      (∃ g : H6, z 0 ^ a * z 1 ^ b * z 2 ^ c * t ^ j = g * z 1 * g⁻¹) ∨
      (∃ g : H6, z 0 ^ a * z 1 ^ b * z 2 ^ c * t ^ j = g * (z 0 * z 1) * g⁻¹) ∨
      (∃ g : H6, z 0 ^ a * z 1 ^ b * z 2 ^ c * t ^ j = g * (z 0 * z 1 * z 2) * g⁻¹) := by
  intro a ha b hb c hc j hj h3 h1
  rw [← welt_eq z t ha hb hc hj] at h3 h1 ⊢
  obtain ⟨r, hr, -, g, hg⟩ := H.word_conj (by omega) h3 h1
  interval_cases r
  · exact Or.inl ⟨g, hg⟩
  · exact Or.inr (Or.inl ⟨g, hg⟩)
  · exact Or.inr (Or.inr ⟨g, hg⟩)

theorem Hyp.conj_w (H : Hyp z t s f0 f2 q) {w : ℕ} (hw : w < 81)
    (h3 : PW (wElt (KS 1) (KS 2) (KS 3) (KS 4) w) 3 = ONE)
    (h1 : wElt (KS 1) (KS 2) (KS 3) (KS 4) w ≠ ONE) (hrec : WR w % 4 = 1) :
    ∃ g : H6, welt z t w = g * z 1 * g⁻¹ := by
  have h3' : welt z t w ^ 3 = 1 := eq_of_enc (by rw [enc6_pow, H.enc_welt, enc_one, h3])
  have h1' : welt z t w ≠ 1 := fun e => h1 (by rw [← H.enc_welt, e, enc_one])
  obtain ⟨r, hr, hr0, g, hg⟩ := H.word_conj hw h3' h1'
  rcases hr0 with rfl | hr0
  · exact ⟨g, hg⟩
  · exact absurd hrec hr0

theorem Hyp.conj_z (H : Hyp z t s f0 f2 q) :
    ∀ i, (∃ g : H6, z i = g * z 1 * g⁻¹) ∧ ∃ g : H6, (z i)⁻¹ = g * z 1 * g⁻¹ := by
  have w1 : ∀ (i : Fin 3) (a b c : ℕ), a < 3 → b < 3 → c < 3 →
      z 0 ^ a * z 1 ^ b * z 2 ^ c * t ^ 0 = z i → welt z t (27 * a + 9 * b + 3 * c + 0) = z i :=
    fun i a b c ha hb hc e => (welt_eq z t ha hb hc (by norm_num)).trans e
  intro i
  fin_cases i
  · refine ⟨?_, ?_⟩
    · obtain ⟨g, hg⟩ := H.conj_w (w := 27) (by norm_num) (by decide +kernel) (by decide +kernel)
        z_recs.1
      exact ⟨g, by rw [← hg]; exact (w1 0 1 0 0 (by norm_num) (by norm_num) (by norm_num)
        (by simp)).symm⟩
    · obtain ⟨g, hg⟩ := H.conj_w (w := 54) (by norm_num) (by decide +kernel) (by decide +kernel)
        z_recs.2.1
      refine ⟨g, ?_⟩
      change (z 0)⁻¹ = g * z 1 * g⁻¹
      rw [← hg, H.z_inv0]
      exact ((welt_eq z t (a := 2) (b := 0) (c := 0) (j := 0) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)).trans (by simp [sq])).symm
  · refine ⟨?_, ?_⟩
    · obtain ⟨g, hg⟩ := H.conj_w (w := 9) (by norm_num) (by decide +kernel) (by decide +kernel)
        z_recs.2.2.1
      exact ⟨g, by rw [← hg]; exact (w1 1 0 1 0 (by norm_num) (by norm_num) (by norm_num)
        (by simp)).symm⟩
    · obtain ⟨g, hg⟩ := H.conj_w (w := 18) (by norm_num) (by decide +kernel) (by decide +kernel)
        z_recs.2.2.2.1
      refine ⟨g, ?_⟩
      change (z 1)⁻¹ = g * z 1 * g⁻¹
      rw [← hg, H.z_inv1]
      exact ((welt_eq z t (a := 0) (b := 2) (c := 0) (j := 0) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)).trans (by simp [sq])).symm
  · refine ⟨?_, ?_⟩
    · obtain ⟨g, hg⟩ := H.conj_w (w := 3) (by norm_num) (by decide +kernel) (by decide +kernel)
        z_recs.2.2.2.2.1
      exact ⟨g, by rw [← hg]; exact (w1 2 0 0 1 (by norm_num) (by norm_num) (by norm_num)
        (by simp)).symm⟩
    · obtain ⟨g, hg⟩ := H.conj_w (w := 6) (by norm_num) (by decide +kernel) (by decide +kernel)
        z_recs.2.2.2.2.2
      refine ⟨g, ?_⟩
      change (z 2)⁻¹ = g * z 1 * g⁻¹
      rw [← hg, H.z_inv2]
      exact ((welt_eq z t (a := 0) (b := 0) (c := 2) (j := 0) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)).trans (by simp [sq])).symm

theorem sp6TransvFacts_kernel : Sp6TransvFacts := by
  unfold Sp6TransvFacts
  refine ⟨⟨⟨ofCode (CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Transv.s0C,
      CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Transv.s0C) (pairCheck_of (by decide +kernel)),
      mat6_ofCode _ _⟩, ⟨ofCode (fl0C, fl0C) (pairCheck_of (by decide +kernel)), mat6_ofCode _ _⟩,
    ⟨ofCode (fl2C, fl2C) (pairCheck_of (by decide +kernel)), mat6_ofCode _ _⟩, fun i => ?_⟩, ?_⟩
  · have h : pairCheck (qCode i, qCode i) = true := by
      refine pairCheck_of ?_
      fin_cases i <;> decide +kernel
    exact ⟨ofCode _ h, mat6_ofCode _ _⟩
  · intro z t s f0 f2 q hz ht hs hf0 hf2 hq
    have H : Hyp z t s f0 f2 q := ⟨hz, ht, hs, hf0, hf2, hq⟩
    exact ⟨H.rels, H.card_cen, fun R hR h2 hN => H.normal_cases hR h2 hN, H.Q_le, H.Q_facts.2.1,
      H.Q_comm, H.Q_sq, H.counts.1, H.counts.2.1, H.counts.2.2.1, H.counts.2.2.2.1,
      H.counts.2.2.2.2, H.mem_commutator, H.filt, H.syl, H.conj_z⟩

end CertificateChecks.KernelMisc.Sp6Transv.Facts

end
