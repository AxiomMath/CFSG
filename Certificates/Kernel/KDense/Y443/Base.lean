
module

public import Certificates.Kernel.KDense.DataOk

@[expose] public section

namespace CertificateChecks.KernelKDense.Y443

open CFSG.KC CFSG.KC.KDense CFSG.KC.KDense.Y443 CFSG.Monster CFSG.Monster.AxisCount CFSG.YGroups.Y443
open CertificateChecks.KernelKDense

theorem item_cong {p : List (List Native.Gen × List Native.Gen)} {S : ℕ → St} {CH : ℕ → ℕ} {nch : ℕ}
    {IT : List ℕ} (hL : pairsLetterOK p = true) (hS : ∀ x < 3, S x = CFSG.KD.KDF.I x)
    (hplan : planOK (words p) CH nch IT = true)
    (hch : ∀ k < nch, chunkOK CFSG.KD.KDF.F CFSG.KD.KDT.T (words p) S (CH k) = true)
    (t : ℕ) (ht : t < IT.length) (hk : IT[t]! / 4 % 2 = 0) :
    (∀ g ∈ (p.getD t ([], [])).1, g.validB = true) ∧ (∀ g ∈ (p.getD t ([], [])).2, g.validB = true) ∧
      Cong5D (Native.evalWord (p.getD t ([], [])).1 (wit (IT[t]! % 4)))
        (Native.evalWord (p.getD t ([], [])).2 (wit (IT[t]! % 4))) := by
  have h := plan_sound data_ok (words p) (words_letterOK hL) S wit (rep_wit hS) CH nch IT hplan
    hch t ht
  rw [words_even, words_odd] at h
  exact ⟨h.1, h.2.1, h.2.2.1 hk⟩

theorem item_ne {p : List (List Native.Gen × List Native.Gen)} {S : ℕ → St} {CH : ℕ → ℕ} {nch : ℕ}
    {IT : List ℕ} (hL : pairsLetterOK p = true) (hS : ∀ x < 3, S x = CFSG.KD.KDF.I x)
    (hplan : planOK (words p) CH nch IT = true)
    (hch : ∀ k < nch, chunkOK CFSG.KD.KDF.F CFSG.KD.KDT.T (words p) S (CH k) = true)
    (t : ℕ) (ht : t < IT.length) (hk : IT[t]! / 4 % 2 = 1) :
    wordLin (p.getD t ([], [])).1 ≠ wordLin (p.getD t ([], [])).2 := by
  have h := plan_sound data_ok (words p) (words_letterOK hL) S wit (rep_wit hS) CH nch IT hplan
    hch t ht
  rw [words_even, words_odd] at h
  obtain ⟨k, hk', hne⟩ := h.2.2.2 hk
  exact wordLin_ne_of_res5_ne h.1 h.2.1 hk' hne

theorem fix3_getD (ws : List (List Native.Gen)) {x j : ℕ} (hx : x < 3) (hj : j < ws.length) :
    (fix3 ws).getD (ws.length * x + j) ([], []) = (ws[j]!, []) := by
  unfold fix3
  simp only [List.getD_eq_getElem?_getD, getElem!_pos ws j hj]
  interval_cases x
  · rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_left (by simp; omega)]
    simp [hj]
  · rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_right (by simp)]
    simp [hj]
  · rw [List.getElem?_append_right (by simp; omega)]
    simp only [List.length_append, List.length_map]
    rw [show ws.length * 2 + j - (ws.length + ws.length) = j by omega]
    simp [hj]

theorem rel_fix3 (ws : List (List Native.Gen)) {S : ℕ → St} {CH : ℕ → ℕ}
    {nch : ℕ} {IT : List ℕ} (hL : pairsLetterOK (fix3 ws) = true)
    (hplan : planOK (words (fix3 ws)) CH nch IT = true)
    (hch : ∀ k < nch, chunkOK CFSG.KD.KDF.F CFSG.KD.KDT.T (words (fix3 ws)) S (CH k) = true)
    (hS : ∀ x < 3, S x = CFSG.KD.KDF.I x)
    (hIT : IT.length = 3 * ws.length)
    (hw : ∀ x < 3, ∀ j < ws.length, IT[ws.length * x + j]! % 4 = x ∧ IT[ws.length * x + j]! / 4 % 2 = 0) :
    ∀ w ∈ ws, wordLin w = 1 := by
  intro w hw'
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hw'
  have h := fun x (hx : x < 3) => item_cong hL hS hplan hch (ws.length * x + j)
    (by rw [hIT]; nlinarith) (hw x hx j hj).2
  have e := eq_of_three (w₁ := ws[j]) (w₂ := []) fun x hx => by
    have hh := h x hx
    rw [fix3_getD ws hx hj, (hw x hx j hj).1, getElem!_pos ws j hj] at hh
    exact hh
  rwa [wordLin_nil] at e

theorem rel_tri (p : List (List Native.Gen × List Native.Gen))
    (hL : pairsLetterOK p = true) {S₀ S₁ S₂ : ℕ → St} {CH₀ CH₁ CH₂ : ℕ → ℕ} {n₀ n₁ n₂ : ℕ} {I₀ I₁ I₂ : List ℕ}
    (p₀ : planOK (words p) CH₀ n₀ I₀ = true) (p₁ : planOK (words p) CH₁ n₁ I₁ = true)
    (p₂ : planOK (words p) CH₂ n₂ I₂ = true)
    (c₀ : ∀ k < n₀, chunkOK CFSG.KD.KDF.F CFSG.KD.KDT.T (words p) S₀ (CH₀ k) = true)
    (c₁ : ∀ k < n₁, chunkOK CFSG.KD.KDF.F CFSG.KD.KDT.T (words p) S₁ (CH₁ k) = true)
    (c₂ : ∀ k < n₂, chunkOK CFSG.KD.KDF.F CFSG.KD.KDT.T (words p) S₂ (CH₂ k) = true)
    (h₀ : ∀ x < 3, S₀ x = CFSG.KD.KDF.I x) (h₁ : ∀ x < 3, S₁ x = CFSG.KD.KDF.I x)
    (h₂ : ∀ x < 3, S₂ x = CFSG.KD.KDF.I x)
    (l₀ : I₀.length = p.length) (l₁ : I₁.length = p.length) (l₂ : I₂.length = p.length)
    (w₀ : ∀ t < p.length, I₀[t]! % 4 = 0 ∧ I₀[t]! / 4 % 2 = 0)
    (w₁ : ∀ t < p.length, I₁[t]! % 4 = 1 ∧ I₁[t]! / 4 % 2 = 0)
    (w₂ : ∀ t < p.length, I₂[t]! % 4 = 2 ∧ I₂[t]! / 4 % 2 = 0) :
    ∀ t < p.length, wordLin (p.getD t ([], [])).1 = wordLin (p.getD t ([], [])).2 := by
  intro t ht
  apply eq_of_three
  intro x hx
  interval_cases x
  · have hh := item_cong hL h₀ p₀ c₀ t (by rw [l₀]; exact ht) (w₀ t ht).2
    rwa [(w₀ t ht).1] at hh
  · have hh := item_cong hL h₁ p₁ c₁ t (by rw [l₁]; exact ht) (w₁ t ht).2
    rwa [(w₁ t ht).1] at hh
  · have hh := item_cong hL h₂ p₂ c₂ t (by rw [l₂]; exact ht) (w₂ t ht).2
    rwa [(w₂ t ht).1] at hh

end CertificateChecks.KernelKDense.Y443

end
