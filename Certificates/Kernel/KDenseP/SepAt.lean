module

public import Certificates.Kernel.KDenseP.Tp3L
public import Certificates.Kernel.KDenseP.AgreeOf
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON11_13.ThirteenCheckDefs

public section

namespace CertificateChecks.KernelKDenseP.TwoPoint

open CFSG.KC CFSG.KC.KDense CFSG.KC.KDenseP CFSG.KC.KDenseP.TwoPoint CFSG.Monster CFSG.Monster.AxisCount
  CFSG.AGLEmbedding.Norton.MON5_7 CFSG.YGroups.Y443 CFSG.YGroups.Y443Native

theorem itemL_sepAt {F : Fix} {MT : MonoTab} {KT TH OCT DU1 : ℕ}
    (hd : dataOKP F MT KT TH OCT DU1 = true)
    {p : List (List Native.Gen × List Native.Gen)} (hL : pairsLetterOK p = true)
    {S : ℕ → St} (hS : ∀ x < 3, S x = CFSG.KD.KDF.I x) {CH : ℕ → ℕ} {nch : ℕ} {IT : List ℕ}
    (hc : ∀ k < nch, chunkOKN 4 2 5 F MT (Y443.words p) S (CH k) = true)
    (hplan : planOKP (Y443.words p) CH nch IT = true) (t : ℕ) (ht : t < IT.length)
    (hk : IT[t]! / 4 % 2 = 1) {r : ℕ} (hr : r < 98280)
    (ho : f20 (CH fld(IT[t]!, 84, 1048575)) 1 = xposK r) :
    DVec.res5 (Native.evalWord (p.getD t ([], [])).1 (KernelKDense.wit (IT[t]! % 4))) (300 + r) ≠
      DVec.res5 (Native.evalWord (p.getD t ([], [])).2 (KernelKDense.wit (IT[t]! % 4))) (300 + r) := by
  have hinit : ∀ x < 3, RepN 4 (KernelKDense.wit x) (S x) := fun x hx =>
    repN_four (KernelKDense.rep_wit hS x hx)
  obtain ⟨-, -, rA, rB, -, hf5, hfn⟩ := itemP_sound (by norm_num) (by norm_num) hd (Y443.words p)
    (KernelKDense.words_letterOK hL) S KernelKDense.wit hinit CH nch IT hplan hc t ht
  obtain ⟨-, hne⟩ := chunkN_kind1 (hc _ hfn) (by rw [hf5]; exact hk)
  rw [KernelKDense.words_even] at rA
  rw [KernelKDense.words_odd] at rB
  rw [ho] at hne
  intro e
  apply hne
  rw [res5_eq, res5_eq, ← rA.1 r hr, ← rB.1 r hr, ← resXq_cast five_dvd, ← resXq_cast five_dvd,
    ZMod.natCast_eq_natCast_iff'] at e
  have hlt : ∀ w : St, resXq 4 5 w (xposK r) < 5 := fun w => by
    rw [resXq_eq]
    exact Nat.mod_lt _ (by norm_num)
  rwa [Nat.mod_eq_of_lt (hlt _), Nat.mod_eq_of_lt (hlt _)] at e

theorem diffX_of_res5 {u v : Native.DVec} {p : ℕ}
    (h : DVec.res5 u (300 + p) ≠ DVec.res5 v (300 + p)) : diffX u v p = true := by
  unfold diffX coordX
  rw [bne_iff_ne]
  intro e
  apply h
  apply res5_eq_of_cf_eq
  unfold cf
  have hE1 : (2 : ℚ) ^ (max u.e v.e) = 2 ^ u.e * 2 ^ (max u.e v.e - u.e) := by
    rw [← pow_add, Nat.add_sub_cancel' (le_max_left _ _)]
  have hE2 : (2 : ℚ) ^ (max u.e v.e) = 2 ^ v.e * 2 ^ (max u.e v.e - v.e) := by
    rw [← pow_add, Nat.add_sub_cancel' (le_max_right _ _)]
  have e' : (u.D.getD (300 + p) 0 : ℚ) * 2 ^ (max u.e v.e - u.e) =
      (v.D.getD (300 + p) 0 : ℚ) * 2 ^ (max u.e v.e - v.e) := by
    exact_mod_cast e
  calc (u.D.getD (300 + p) 0 : ℚ) / 2 ^ u.e
      = (u.D.getD (300 + p) 0 : ℚ) * 2 ^ (max u.e v.e - u.e) / 2 ^ (max u.e v.e) := by
        rw [hE1]; field_simp
    _ = (v.D.getD (300 + p) 0 : ℚ) * 2 ^ (max u.e v.e - v.e) / 2 ^ (max u.e v.e) := by rw [e']
    _ = (v.D.getD (300 + p) 0 : ℚ) / 2 ^ v.e := by rw [hE2]; field_simp

theorem moveCheck_of_sepL {w : List Native.Gen}
    (h : (∀ g ∈ w, g.validB = true) ∧ (∀ g ∈ ([] : List Native.Gen), g.validB = true) ∧
      EdgeNoncomm.moveCheckAux (Native.evalWord w (aV ())) (Native.evalWord [] (aV ())) = true) :
    EdgeNoncomm.moveCheck w (aV ()) = true := by
  unfold EdgeNoncomm.moveCheck
  rw [Bool.and_eq_true]
  exact ⟨List.all_eq_true.2 h.1, h.2.2⟩

theorem interp_ne_of_moveCheckAux {u v : Native.DVec}
    (h : EdgeNoncomm.moveCheckAux u v = true) : interp u ≠ interp v := by
  unfold EdgeNoncomm.moveCheckAux at h
  obtain ⟨k, hk, hne⟩ := List.any_eq_true.1 h
  rw [List.mem_range] at hk
  intro e
  have hc := cf_eq_of_interp_eq e hk
  unfold cf at hc
  have hu0 : (2 : ℚ) ^ u.e ≠ 0 := pow_ne_zero _ two_ne_zero
  have hv0 : (2 : ℚ) ^ v.e ≠ 0 := pow_ne_zero _ two_ne_zero
  rw [div_eq_div_iff hu0 hv0] at hc
  rw [bne_iff_ne] at hne
  exact hne (by exact_mod_cast hc)

theorem moveCheckAux_of_interp_ne {u v : Native.DVec}
    (hu : u.D.size = 196884) (hv : v.D.size = 196884) (h : interp u ≠ interp v) :
    EdgeNoncomm.moveCheckAux u v = true := by
  unfold EdgeNoncomm.moveCheckAux
  rw [List.any_eq_true]
  by_contra hn
  push Not at hn
  apply h
  apply interp_eq_of_cf
  intro k
  unfold cf
  have hu0 : (2 : ℚ) ^ u.e ≠ 0 := pow_ne_zero _ two_ne_zero
  have hv0 : (2 : ℚ) ^ v.e ≠ 0 := pow_ne_zero _ two_ne_zero
  rw [div_eq_div_iff hu0 hv0]
  by_cases hk : k < 196884
  · have e := hn k (List.mem_range.2 hk)
    simp only [bne_iff_ne, ne_eq, not_not] at e
    exact_mod_cast e
  · have h1 : u.D.getD k 0 = 0 := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)]
      rfl
    have h2 : v.D.getD k 0 = 0 := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)]
      rfl
    rw [h1, h2]
    simp

theorem moveCheck_of_suffix {w s : List Native.Gen}
    (hw : ∀ g ∈ w ++ s, g.validB = true) (hs : ∀ g ∈ s, g.validB = true)
    (h : EdgeNoncomm.moveCheckAux (Native.evalWord (w ++ s) (aV ())) (Native.evalWord s (aV ())) = true) :
    EdgeNoncomm.moveCheck w (aV ()) = true := by
  have hw' : ∀ g ∈ w, g.validB = true := fun g hg => hw g (List.mem_append_left _ hg)
  have hne := interp_ne_of_moveCheckAux h
  rw [evalWord_sound _ hw, evalWord_sound _ hs, wordLin_append, LinearEquiv.mul_apply] at hne
  unfold EdgeNoncomm.moveCheck
  rw [Bool.and_eq_true]
  refine ⟨List.all_eq_true.2 hw', moveCheckAux_of_interp_ne
    (KernelKDenseP.size_evalWordC _ w _ KernelKDenseP.size_aV) KernelKDenseP.size_aV fun e => hne ?_⟩
  rw [← evalWord_sound _ hw', e]

theorem tp3B_eqs
    {F : Fix} {MT : MonoTab} {KT TH OCT DU1 : ℕ} (hd : dataOKP F MT KT TH OCT DU1 = true)
    (eqs nes : List (List Native.Gen × List Native.Gen)) (hL : pairsLetterOK (tp3 eqs nes) = true)
    {S : ℕ → St} (hS : ∀ x < 3, S x = CFSG.KD.KDF.I x) {CH : ℕ → ℕ} {nch : ℕ} {IT : List ℕ}
    (hc : ∀ k < nch, chunkOKN 4 2 5 F MT (Y443.words (tp3 eqs nes)) S (CH k) = true)
    (hplan : planOKP (Y443.words (tp3 eqs nes)) CH nch IT = true)
    (hwk : wkOK (IT.take (3 * eqs.length)) (tpWK eqs.length 0) = true) :
    agreeAll eqs = true := by
  obtain ⟨hl, hk⟩ := wkOK_spec hwk
  rw [tpWK_length] at hl
  have it := itemL hd hL hS hc hplan
  have key : ∀ x < 3, ∀ j < eqs.length, (∀ g ∈ eqs[j]!.1, g.validB = true) ∧
      (∀ g ∈ eqs[j]!.2, g.validB = true) ∧
      Cong5D (Native.evalWord eqs[j]!.1 (KernelKDense.wit x))
        (Native.evalWord eqs[j]!.2 (KernelKDense.wit x)) := by
    intro x hx j hj
    have ht' : eqs.length * x + j < (IT.take (3 * eqs.length)).length := by rw [hl]; nlinarith
    have ht : eqs.length * x + j < IT.length :=
      lt_of_lt_of_le ht' (List.length_take_le' _ _)
    obtain ⟨k1, k2⟩ := hk _ ht'
    rw [tpWK_getD_eq hx hj] at k1 k2
    have e : (IT.take (3 * eqs.length))[eqs.length * x + j]! = IT[eqs.length * x + j]! := by
      have hlt : eqs.length * x + j < 3 * eqs.length := by nlinarith
      simp only [List.getElem!_eq_getElem?_getD, List.getElem?_take_of_lt hlt]
    rw [e] at k1 k2
    obtain ⟨v1, v2, c, -⟩ := it _ ht
    rw [tp3_getD_eq eqs nes hx hj, ← getElem!_pos eqs j hj] at v1 v2 c
    rw [k1] at c
    exact ⟨v1, v2, c k2⟩
  refine List.all_eq_true.2 fun e he => ?_
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem he
  have k0 := key 0 (by norm_num) j hj
  rw [← getElem!_pos eqs j hj]
  exact KernelKDenseP.agree_of_wordLin k0.1 k0.2.1
    (KernelKDense.Y443.eq_of_three fun x hx => key x hx j hj)

theorem eqWords3C_eq_agree (w₁ w₂ : List Native.Gen) :
    CFSG.AGLEmbedding.Norton.MON11_13.eqWords3C (Native.mkCtx ()) w₁ w₂ = agree w₁ w₂ := by
  unfold CFSG.AGLEmbedding.Norton.MON11_13.eqWords3C CFSG.AGLEmbedding.Norton.MON11_13.eqWordsC agree
    Native.evalWord
  cases (w₁.all fun g => g.validB) <;> cases (w₂.all fun g => g.validB) <;> simp

end CertificateChecks.KernelKDenseP.TwoPoint

end
