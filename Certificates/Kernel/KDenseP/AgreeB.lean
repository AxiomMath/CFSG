module

public import Certificates.Kernel.KDenseP.Tp3L
public import Certificates.Kernel.KDenseP.AgreeOf

public section

namespace CertificateChecks.KernelKDenseP.TwoPoint

open CFSG.KC CFSG.KC.KDense CFSG.KC.KDenseP CFSG.KC.KDenseP.TwoPoint CFSG.Monster CFSG.Monster.AxisCount
  CFSG.AGLEmbedding.Norton.MON5_7 CFSG.YGroups.Y443 CFSG.YGroups.Y443Native

theorem tp3B_sound
    {F : Fix} {MT : MonoTab} {KT TH OCT DU1 : ℕ} (hd : dataOKP F MT KT TH OCT DU1 = true)
    (eqs nes : List (List Native.Gen × List Native.Gen)) (hL : pairsLetterOK (tp3 eqs nes) = true)
    {S : ℕ → St} (hS : ∀ x < 3, S x = CFSG.KD.KDF.I x) {CH : ℕ → ℕ} {nch : ℕ} {IT : List ℕ}
    (hc : ∀ k < nch, chunkOKN 4 2 5 F MT (Y443.words (tp3 eqs nes)) S (CH k) = true)
    (hplan : planOKP (Y443.words (tp3 eqs nes)) CH nch IT = true)
    (hwk : wkOK IT (tpWK eqs.length nes.length) = true) :
    agreeAll eqs = true ∧ ∀ e ∈ nes, (∀ g ∈ e.1, g.validB = true) ∧ (∀ g ∈ e.2, g.validB = true) ∧
      EdgeNoncomm.moveCheckAux (Native.evalWord e.1 (aV ())) (Native.evalWord e.2 (aV ())) = true := by
  have hfacts := tp3L_sound hd eqs nes hL hS hc hplan hwk
  obtain ⟨hl, hk⟩ := wkOK_spec hwk
  rw [tpWK_length] at hl
  have it := itemL hd hL hS hc hplan
  refine ⟨List.all_eq_true.2 fun e he => ?_, fun e he => ?_⟩
  · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem he
    have ht : eqs.length * 0 + j < IT.length := by rw [hl]; omega
    obtain ⟨v1, v2, -, -⟩ := it _ ht
    rw [tp3_getD_eq eqs nes (by norm_num) hj] at v1 v2
    exact KernelKDenseP.agree_of_wordLin v1 v2 (hfacts.1 _ he)
  · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem he
    have ht : eqs.length * 3 + j < IT.length := by rw [hl]; omega
    obtain ⟨k1, k2⟩ := hk _ ht
    rw [tpWK_getD_ne hj] at k1 k2
    obtain ⟨v1, v2, -, n⟩ := it _ ht
    rw [tp3_getD_ne eqs nes hj] at v1 v2 n
    obtain ⟨k, hk', hne⟩ := n k2
    rw [k1] at hne
    exact ⟨v1, v2, KernelKDenseP.moveCheckAux_of_res5 hk' hne⟩

end CertificateChecks.KernelKDenseP.TwoPoint

end
