module

public import Certificates.Kernel.PropA.Cover

public section

namespace CertificateChecks.KernelPropA

open Equiv Subgroup CFSG.EvenSporadicStandard.M12Std.PropA
  CFSG.EvenSporadicStandard.M12Std.PropA.Native

theorem pa450010_wordP_append (b : Bool) (u v : List Int) :
    wordP (pa450010gK b) 4 (u ++ v) = wordP (pa450010gK b) 4 u * wordP (pa450010gK b) 4 v := by
  unfold wordP CFSG.Sporadic.Th.wordG
  rw [List.map_append, List.prod_append]

theorem pa450010_wordP_x (b : Bool) : wordP (pa450010gK b) 4 pa450010wx = pa450010x :=
  (pa450010wv_eq_wordP b 4 _ (pa450010_wx_letters 4 (by norm_num))).symm.trans
    (pa450010wv_wx b (by norm_num))

theorem pa450010_wordP_3 (b : Bool) : wordP (pa450010gK b) 4 [3] = pG b := by
  simp [wordP, CFSG.Sporadic.Th.wordG, letterG, pa450010gK]

theorem pa450010_wordP_4 (b : Bool) : wordP (pa450010gK b) 4 [4] = pT := by
  simp [wordP, CFSG.Sporadic.Th.wordG, letterG, pa450010gK]

theorem pa450010_rep_eq (b : Bool) :
    pa450010rep b 2 = pa450010x ∧ pa450010rep b 3 = pa450010x * pT ∧
      pa450010rep b 4 = pG b ∧ pa450010rep b 5 = pG b * pT := by
  have hl : ∀ wd : List Int, (∀ l ∈ wd, l ≠ 0 ∧ l.natAbs ≤ 4) →
      pa450010wv b 4 wd = wordP (pa450010gK b) 4 wd := pa450010wv_eq_wordP b 4
  have h4 : ∀ l ∈ ([4] : List Int), l ≠ 0 ∧ l.natAbs ≤ 4 := by simp
  have h3 : ∀ l ∈ ([3] : List Int), l ≠ 0 ∧ l.natAbs ≤ 4 := by simp
  have hx := pa450010_wx_letters 4 (by norm_num)
  refine ⟨pa450010wv_wx b (by norm_num), ?_, ?_, ?_⟩
  · change pa450010wv b 4 (pa450010wx ++ [4]) = _
    rw [hl _ (fun l h => (List.mem_append.1 h).elim (hx l) (h4 l)), pa450010_wordP_append,
      pa450010_wordP_x, pa450010_wordP_4]
  · change pa450010wv b 4 [3] = _
    rw [hl _ h3, pa450010_wordP_3]
  · change pa450010wv b 4 ([3] ++ [4]) = _
    rw [hl _ (fun l h => (List.mem_append.1 h).elim (h3 l) (h4 l)), pa450010_wordP_append,
      pa450010_wordP_3, pa450010_wordP_4]

theorem pa450010_pT_ne_one : pT ≠ 1 := fun h => pT_not_mem_D28 (h ▸ one_mem _)

theorem pa450010_sq_of_order_two {y : Perm (Fin 28)} (hy : orderOf y = 2) : y * y = 1 ∧ y ≠ 1 := by
  refine ⟨by rw [← pow_two, ← hy]; exact pow_orderOf_eq_one y, ?_⟩
  rintro rfl
  rw [orderOf_one] at hy
  exact absurd hy (by norm_num)

theorem pa450010_ne_pT (b : Bool) {y : Perm (Fin 28)}
    (hd : Nat.card ↥(K28 b ⊓ centralizer ({y} : Set (Perm (Fin 28)))) ∣ 960) : y ≠ pT := by
  rintro rfl
  have e : K28 b ⊓ centralizer ({pT} : Set (Perm (Fin 28))) = K28 b := by
    exact inf_eq_left.2 fun k hk =>
      mem_centralizer_singleton_iff.2 (pT_commute_of_mem_K28 b k hk)
  rw [e, card_K28] at hd
  norm_num at hd

theorem pa450010_G2_red (b : Bool) {y : Perm (Fin 28)}
    (hy : y ∈ K28 b) (h2 : orderOf y = 2)
    (hd : Nat.card ↥(K28 b ⊓ centralizer ({y} : Set (Perm (Fin 28)))) ∣ 960) :
    ∃ h ∈ K28 b, h * pa450010x * h⁻¹ = y ∨ h * (pa450010x * pT) * h⁻¹ = y ∨
      (b = false ∧ (h * pG false * h⁻¹ = y ∨ h * (pG false * pT) * h⁻¹ = y)) := by
  obtain ⟨hyy, hy1⟩ := pa450010_sq_of_order_two h2
  obtain ⟨i, hi, ⟨h, hh, e⟩, hsz⟩ := pa450010_cover b hy (Or.inl hyy) hy1 (pa450010_ne_pT b hd)
  obtain ⟨r2, r3, r4, r5⟩ := pa450010_rep_eq b
  have hsq : ∀ r : Perm (Fin 28), h * r * h⁻¹ = y → r * r = 1 := by
    intro r hr
    have e2 : h * (r * r) * h⁻¹ = 1 := by
      rw [← hyy, ← hr]
      group
    have e3 : r * r = h⁻¹ * (h * (r * r) * h⁻¹) * h := by group
    rw [e3, e2]
    group
  have hTT : pT * pT = 1 := pT_mul_self
  have hGT := pG_comm_pT true
  have hGG := pG_mul_self true
  simp only [if_true] at hGG
  interval_cases i
  · have hc : Nat.card ↥(K28 b ⊓ centralizer ({y} : Set (Perm (Fin 28)))) = 768 := by
      change 495 * _ = 380160 at hsz
      omega
    rw [hc] at hd
    norm_num at hd
  · have hc : Nat.card ↥(K28 b ⊓ centralizer ({y} : Set (Perm (Fin 28)))) = 768 := by
      change 495 * _ = 380160 at hsz
      omega
    rw [hc] at hd
    norm_num at hd
  · rw [r2] at e
    exact ⟨h, hh, Or.inl e⟩
  · rw [r3] at e
    exact ⟨h, hh, Or.inr (Or.inl e)⟩
  · rw [r4] at e
    cases b
    · exact ⟨h, hh, Or.inr (Or.inr ⟨rfl, Or.inl e⟩)⟩
    · have := hsq _ e
      rw [hGG] at this
      exact absurd this pa450010_pT_ne_one
  · rw [r5] at e
    cases b
    · exact ⟨h, hh, Or.inr (Or.inr ⟨rfl, Or.inr e⟩)⟩
    · have := hsq _ e
      have e4 : pG true * pT * (pG true * pT) = pG true * pG true * (pT * pT) := by
        rw [mul_assoc, ← mul_assoc pT, ← hGT]
        group
      rw [e4, hGG, hTT, mul_one] at this
      exact absurd this pa450010_pT_ne_one

theorem pa450010_G1_red (b : Bool) {J : Set (Perm (Fin 28))}
    (hr : ∀ i < 6, pa450010rep b i * pa450010rep b i = 1 → ∃ c ∈ K28 b,
      c * pa450010rep b i * c⁻¹ ∈ centralizer ({pa450010x} : Set (Perm (Fin 28))) ∧
        c * pa450010rep b i * c⁻¹ ∉ centralizer J) :
    ∀ w ∈ K28 b, orderOf w = 2 → w ≠ pT → ∃ c ∈ K28 b,
      c * w * c⁻¹ ∈ centralizer ({pa450010x} : Set (Perm (Fin 28))) ∧
        c * w * c⁻¹ ∉ centralizer J := by
  intro w hw h2 ht
  obtain ⟨hww, hw1⟩ := pa450010_sq_of_order_two h2
  obtain ⟨i, hi, ⟨h, hh, e⟩, -⟩ := pa450010_cover b hw (Or.inl hww) hw1 ht
  have hrr : pa450010rep b i * pa450010rep b i = 1 := by
    have e2 : h * (pa450010rep b i * pa450010rep b i) * h⁻¹ = 1 := by
      rw [← hww, ← e]
      group
    have e3 : pa450010rep b i * pa450010rep b i =
        h⁻¹ * (h * (pa450010rep b i * pa450010rep b i) * h⁻¹) * h := by group
    rw [e3, e2]
    group
  obtain ⟨c, hc, h1, h2⟩ := hr i hi hrr
  have e5 : c * h⁻¹ * w * (c * h⁻¹)⁻¹ = c * pa450010rep b i * c⁻¹ := by
    rw [← e]
    group
  exact ⟨c * h⁻¹, (K28 b).mul_mem hc ((K28 b).inv_mem hh), by rw [e5]; exact h1,
    by rw [e5]; exact h2⟩

end CertificateChecks.KernelPropA

end
