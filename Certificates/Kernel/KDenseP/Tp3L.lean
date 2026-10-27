module

public import Certificates.Kernel.KDenseP.TwoPoint.Base

public section

namespace CertificateChecks.KernelKDenseP.TwoPoint

open CFSG.KC CFSG.KC.KDense CFSG.KC.KDenseP CFSG.KC.KDenseP.TwoPoint CFSG.Monster
  CFSG.Monster.AxisCount

theorem itemL {F : Fix} {MT : MonoTab} {KT TH OCT DU1 : ℕ} (hd : dataOKP F MT KT TH OCT DU1 = true)
    {p : List (List Native.Gen × List Native.Gen)} (hL : pairsLetterOK p = true)
    {S : ℕ → St} (hS : ∀ x < 3, S x = CFSG.KD.KDF.I x) {CH : ℕ → ℕ} {nch : ℕ} {IT : List ℕ}
    (hc : ∀ k < nch, chunkOKN 4 2 5 F MT (Y443.words p) S (CH k) = true)
    (hplan : planOKP (Y443.words p) CH nch IT = true) (t : ℕ) (ht : t < IT.length) :
    (∀ g ∈ (p.getD t ([], [])).1, g.validB = true) ∧ (∀ g ∈ (p.getD t ([], [])).2, g.validB = true) ∧
      (IT[t]! / 4 % 2 = 0 → Cong5D
        (Native.evalWord (p.getD t ([], [])).1 (KernelKDense.wit (IT[t]! % 4)))
        (Native.evalWord (p.getD t ([], [])).2 (KernelKDense.wit (IT[t]! % 4)))) ∧
      (IT[t]! / 4 % 2 = 1 → ∃ k < 196884,
        DVec.res5 (Native.evalWord (p.getD t ([], [])).1 (KernelKDense.wit (IT[t]! % 4))) k ≠
          DVec.res5 (Native.evalWord (p.getD t ([], [])).2 (KernelKDense.wit (IT[t]! % 4))) k) := by
  have hinit : ∀ x < 3, RepN 4 (KernelKDense.wit x) (S x) := fun x hx =>
    repN_four (KernelKDense.rep_wit hS x hx)
  obtain ⟨vA, vB, he, hn⟩ := planP_sound (by norm_num) (by norm_num) five_dvd hd (Y443.words p)
    (KernelKDense.words_letterOK hL) S KernelKDense.wit hinit CH nch IT hplan hc t ht
  rw [KernelKDense.words_even] at vA he hn
  rw [KernelKDense.words_odd] at vB he hn
  refine ⟨vA, vB, fun hk k hk' => ?_, fun hk => ?_⟩
  · rw [res5_eq, res5_eq, he hk k hk']
  · obtain ⟨k, hk', hne⟩ := hn hk
    exact ⟨k, hk', by rwa [res5_eq, res5_eq]⟩

theorem tp3L_sound
    {F : Fix} {MT : MonoTab} {KT TH OCT DU1 : ℕ} (hd : dataOKP F MT KT TH OCT DU1 = true)
    (eqs nes : List (List Native.Gen × List Native.Gen)) (hL : pairsLetterOK (tp3 eqs nes) = true)
    {S : ℕ → St} (hS : ∀ x < 3, S x = CFSG.KD.KDF.I x) {CH : ℕ → ℕ} {nch : ℕ} {IT : List ℕ}
    (hc : ∀ k < nch, chunkOKN 4 2 5 F MT (Y443.words (tp3 eqs nes)) S (CH k) = true)
    (hplan : planOKP (Y443.words (tp3 eqs nes)) CH nch IT = true)
    (hwk : wkOK IT (tpWK eqs.length nes.length) = true) :
    (∀ e ∈ eqs, wordLin e.1 = wordLin e.2) ∧ ∀ e ∈ nes, wordLin e.1 ≠ wordLin e.2 := by
  obtain ⟨hl, hk⟩ := wkOK_spec hwk
  rw [tpWK_length] at hl
  have it := itemL hd hL hS hc hplan
  refine ⟨fun e he => ?_, fun e he => ?_⟩
  · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem he
    apply KernelKDense.Y443.eq_of_three
    intro x hx
    have ht : eqs.length * x + j < IT.length := by rw [hl]; nlinarith
    obtain ⟨k1, k2⟩ := hk _ ht
    rw [tpWK_getD_eq hx hj] at k1 k2
    obtain ⟨v1, v2, c, -⟩ := it _ ht
    rw [tp3_getD_eq eqs nes hx hj] at v1 v2 c
    rw [k1] at c
    exact ⟨v1, v2, c k2⟩
  · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem he
    have ht : eqs.length * 3 + j < IT.length := by rw [hl]; omega
    obtain ⟨k1, k2⟩ := hk _ ht
    rw [tpWK_getD_ne hj] at k1 k2
    obtain ⟨v1, v2, -, n⟩ := it _ ht
    rw [tp3_getD_ne eqs nes hj] at v1 v2 n
    obtain ⟨k, hk', hne⟩ := n k2
    exact wordLin_ne_of_res5_ne v1 v2 hk' hne

end CertificateChecks.KernelKDenseP.TwoPoint

end
