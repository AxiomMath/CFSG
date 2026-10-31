
module

public import CFSG.Sporadic.Th.KernelCentJBase
public import Certificates.Kernel.ThCent.Assemble
public import Certificates.Kernel.ThCent.Shared
public import Certificates.Kernel.ThCent.C3A
public import Certificates.Kernel.ThCent.C3B
public import Certificates.Kernel.ThCent.C7A
public import Certificates.Kernel.ThCent.C7B
public import Certificates.Kernel.ThCent.C13A
public import Certificates.Kernel.ThCent.Wit

@[expose] public section

namespace CertificateChecks.KernelThCent

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Kernel CFSG.Sporadic.Bridge CFSG.KC.Th CFSG.KC.ThCent
  CFSG.KC.Th.Spec CFSG.KC.Th.Spec.DceStr CFSG.KD CFSG.KD.ThCent TauCeti

local notation "𝕄" g:max =>
  ((Subtype.val g : GL (Fin 248) (ZMod 2)) : Matrix (Fin 248) (Fin 248) (ZMod 2))

theorem hnT : thcDceData.ThB_nT ≤ 2048 * 18 := by
  rw [thcDce_nT]
  decide
theorem hNB : thcDceData.ThB_NB = 1 := by
  rw [thcDce_NB]
  rfl

theorem hsh : sharedOK thcDceData.ThB_LT BF thcDceData.ThA_CB CJ thcDceData.ThB_om = true := by
  rw [thcDce_LT, thcDce_CB, thcDce_om]
  exact Chk.shared

theorem hsv : ∀ i < 9, svChunk SV PI thcDceData.ThB_OB thcDceData.ThB_osh thcDceData.ThB_owd thcDceData.ThB_om
    thcDceData.ThB_NO i = true := by
  rw [thcDce_OB, thcDce_osh, thcDce_owd, thcDce_om, thcDce_NO]
  exact Chk.sv.all

theorem hpt : ∀ i < 9, ptChunk SV QI thcDceData.ThB_OB thcDceData.ThB_osh thcDceData.ThB_owd thcDceData.ThB_om
    thcDceData.ThB_NO i = true := by
  rw [thcDce_OB, thcDce_osh, thcDce_owd, thcDce_om, thcDce_NO]
  exact Chk.pt.all

noncomputable def nOf (OR1 OR2 OR3 OR4 OR5 OR6 OR7 OR8 OR9 OR10 : List ℕ) : Fin 11 → ℕ :=
  ![0, sumN OR5, sumN OR7, sumN OR6, sumN OR9, sumN OR8, sumN OR3, sumN OR2, sumN OR4,
    sumN OR10, sumN OR1]

theorem or_counts {o r : ℕ} {OR1 OR2 OR3 OR4 OR5 OR6 OR7 OR8 OR9 OR10 : List ℕ}
    (h1 : ∀ i < 18, orChunk ThB.E1 36864 o r OR1 i = true)
    (h2 : ∀ i < 7, orChunk ThB.E2 13824 o r OR2 i = true)
    (h3 : ∀ i < 1, orChunk ThB.E3 486 o r OR3 i = true)
    (h4 : ∀ i < 1, orChunk ThB.E4 288 o r OR4 i = true)
    (h5 : ∀ i < 1, orChunk ThB.E5 54 o r OR5 i = true)
    (h6 : ∀ i < 1, orChunk ThB.E6 6 o r OR6 i = true)
    (h7 : ∀ i < 1, orChunk ThB.E7 126 o r OR7 i = true)
    (h8 : ∀ i < 1, orChunk ThB.E8 78 o r OR8 i = true)
    (h9 : ∀ i < 1, orChunk ThB.E9 72 o r OR9 i = true)
    (h10 : ∀ i < 2, orChunk ThB.E10 3528 o r OR10 i = true) :
    ∀ D' : Fin 11, D' ≠ 0 → ((Finset.range (mD D')).filter fun j =>
      ordRank o r (DceS.mat (tabB thcDceData (cosetOrder D')) j) = true).card ≤
        nOf OR1 OR2 OR3 OR4 OR5 OR6 OR7 OR8 OR9 OR10 D' := by
  intro D' hD0
  fin_cases D' <;>
    simp only [nOf, tabB, cosetOrder, thcDce_E1, thcDce_E2, thcDce_E3, thcDce_E4, thcDce_E5,
      thcDce_E6, thcDce_E7, thcDce_E8, thcDce_E9, thcDce_E10, Fin.zero_eta, Fin.isValue,
      Matrix.cons_val, ne_eq] at hD0 ⊢
  · exact absurd trivial hD0
  · exact or_card_le (by decide) h5
  · exact or_card_le (by decide) h7
  · exact or_card_le (by decide) h6
  · exact or_card_le (by decide) h9
  · exact or_card_le (by decide) h8
  · exact or_card_le (by decide) h3
  · exact or_card_le (by decide) h2
  · exact or_card_le (by decide) h4
  · exact or_card_le (by decide) h10
  · exact or_card_le (by decide) h1

theorem not_conj_of_rank {w w' : List ℕ} {o r r' : ℕ} (hr : r ≠ r') (ht : wval gen w ∈ K)
    (ht' : wval gen w' ∈ K)
    (hinv : ∀ g ∈ K, ∀ w'' : List ℕ, (∀ c ∈ w'', c < 14) →
      g * wval gen w * g⁻¹ = wval gen w'' → ordRank o r (wordM ThB.LT w'') = true)
    (hw' : ∀ c ∈ w', c < 14) (hr' : ordRank o r' (wordM ThB.LT w') = true) :
    ¬IsConj (⟨wval gen w, ht⟩ : K) ⟨wval gen w', ht'⟩ := by
  intro hc
  obtain ⟨g, hg⟩ := isConj_iff.1 hc
  have e : (g : P) * wval gen w * (g : P)⁻¹ = wval gen w' := congrArg Subtype.val hg
  have h1 := ordRank_spec (hinv g g.2 w' hw' e)
  have h2 := ordRank_spec hr'
  exact hr (h1.2.symm.trans h2.2)


end CertificateChecks.KernelThCent

end
