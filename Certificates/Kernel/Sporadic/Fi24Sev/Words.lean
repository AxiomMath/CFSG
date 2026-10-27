module

public import Certificates.Kernel.Sporadic.Fi24ThreeO.Group
public import Certificates.Kernel.Sporadic.Fi24Seven.Glue
public import CFSG.Certificates.Kernel.Spor.Fi24SevSound
public import CFSG.Sporadic.FischerOddCore.Fi24AlmostSimple
public import CFSG.Sporadic.FischerOddCore.Fi24R2CompBase
public import CFSG.Sporadic.FischerOddCore.FischerOuterBasic
public import CFSG.Sporadic.Schreier.MathieuOddCoreWords

public section

namespace CFSG.KD.Fi24Sev.Words

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three
open CFSG.Sporadic.Fi24 (J gs)
open CFSG.Perm CFSG.Perm.Native CFSG.Sporadic.Th CFSG.KC CFSG.KC.Fi24ThreeO CFSG.KC.Fi24Sev
  CFSG.KS.Fi24Net CFSG.KS.Fi24ThreeO CFSG.KS.Fi24Sev CFSG.KD.Fi24Net CFSG.KD.Fi24Kit
  CFSG.KD.Fi24ThreeO.Group CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24SevenNative
  CFSG.KC.SlpM

attribute [local instance] CFSG.Sporadic.Fi24.rAction


local notation "WG" => CFSG.Sporadic.Fi23.slpG CFSG.Sporadic.Fi24.genG fi24SevenData.words

theorem findU_spec {sl : List (ℕ × List ℕ × List ℕ)} {k : ℕ} (h : ∃ e ∈ sl, e.1 = k) :
    ∃ e ∈ sl, e.1 = k ∧ findU sl k = e.2.2 := by
  induction sl with
  | nil => obtain ⟨e, he, -⟩ := h; exact absurd he List.not_mem_nil
  | cons a l ih =>
    by_cases hk : a.1 = k
    · refine ⟨a, List.mem_cons_self, hk, ?_⟩
      change Bool.rec (findU l k) a.2.2 (Nat.beq a.1 k) = a.2.2
      rw [hk, Nat.beq_refl]
    · obtain ⟨e, he, hek⟩ := h
      rcases List.mem_cons.1 he with rfl | he'
      · exact absurd hek hk
      · obtain ⟨e', he'', h1, h2⟩ := ih ⟨e, he', hek⟩
        refine ⟨e', List.mem_cons_of_mem a he'', h1, ?_⟩
        change Bool.rec (findU l k) a.2.2 (Nat.beq a.1 k) = e'.2.2
        rw [show Nat.beq a.1 k = false from by
          cases e : Nat.beq a.1 k
          · rfl
          · exact absurd (Nat.eq_of_beq_eq_true e) hk]
        exact h2

theorem lIf_true {t e : List ℕ} : lIf true t e = t := rfl
theorem lIf_false {t e : List ℕ} : lIf false t e = e := rfl

theorem beq_of {a b : ℕ} (h : a = b) : Nat.beq a b = true := by rw [h, Nat.beq_refl]
theorem beq_ne {a b : ℕ} (h : a ≠ b) : Nat.beq a b = false := by
  cases e : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true e) h
theorem ble_of {a b : ℕ} (h : a ≤ b) : Nat.ble a b = true := Nat.ble_eq.mpr h
theorem ble_ne {a b : ℕ} (h : ¬ a ≤ b) : Nat.ble a b = false := by
  cases e : Nat.ble a b
  · rfl
  · exact absurd (Nat.ble_eq.mp e) h

theorem wordElt_single (l : ℕ) : wordElt [l] = pairG gs l := by
  rw [wordElt_cons, wordElt_nil, mul_one]

theorem genG_letter (z : ℕ) (hz2 : 2 ≤ z) (hz5 : z ≤ 5) :
    wordElt (letU [] z) = CFSG.Sporadic.Fi24.genG (decC z) := by
  have g0 : pairG gs 0 = CFSG.Sporadic.Fi24.a := by simp [pairG, CFSG.Sporadic.Fi24.gs_zero]
  have g1 : pairG gs 1 = CFSG.Sporadic.Fi24.a⁻¹ := by simp [pairG, CFSG.Sporadic.Fi24.gs_zero]
  have g2 : pairG gs 2 = CFSG.Sporadic.Fi24.b := by simp [pairG, CFSG.Sporadic.Fi24.gs_one]
  have g3 : pairG gs 3 = CFSG.Sporadic.Fi24.b⁻¹ := by simp [pairG, CFSG.Sporadic.Fi24.gs_one]
  interval_cases z <;> simp [letU, lIf, wordElt_single, g0, g1, g2, g3, decC,
    CFSG.Sporadic.Fi24.genG, Nat.ble, Nat.beq]

theorem letU_lt {sl : List (ℕ × List ℕ × List ℕ)} (hsl : ∀ e ∈ sl, ∀ l ∈ e.2.2, l < 26) (z : ℕ) :
    ∀ l ∈ letU sl z, l < 26 := by
  intro l hl
  unfold letU at hl
  by_cases h5 : z ≤ 5
  · rw [ble_of h5, lIf_true] at hl
    by_cases h3 : z ≤ 3
    · rw [ble_of h3, lIf_true] at hl
      by_cases h2 : z = 2
      · rw [beq_of h2, lIf_true] at hl; simp at hl; omega
      · rw [beq_ne h2, lIf_false] at hl; simp at hl; omega
    · rw [ble_ne h3, lIf_false] at hl
      by_cases h4 : z = 4
      · rw [beq_of h4, lIf_true] at hl; simp at hl; omega
      · rw [beq_ne h4, lIf_false] at hl; simp at hl; omega
  · rw [ble_ne h5, lIf_false] at hl
    have hf : ∀ l ∈ findU sl (Nat.sub (Nat.shiftRight z 1) 3), l < 26 := by
      intro l hl
      by_cases hk : ∃ e ∈ sl, e.1 = Nat.sub (Nat.shiftRight z 1) 3
      · obtain ⟨e, he, -, he2⟩ := findU_spec hk
        rw [he2] at hl
        exact hsl e he l hl
      · have key : ∀ (L : List (ℕ × List ℕ × List ℕ)) (k : ℕ), (¬ ∃ e ∈ L, e.1 = k) → findU L k = [] := by
          intro L k
          induction L with
          | nil => intro _; rfl
          | cons a l' ih =>
            intro hk'
            change Bool.rec (findU l' k) a.2.2 (Nat.beq a.1 k) = []
            rw [beq_ne (fun e => hk' ⟨a, List.mem_cons_self, e⟩)]
            exact ih (fun ⟨e, he, h⟩ => hk' ⟨e, List.mem_cons_of_mem a he, h⟩)
        rw [key sl _ hk] at hl
        exact absurd hl List.not_mem_nil
    cases e : Nat.beq (Nat.land z 1) 0
    · rw [e, lIf_false] at hl
      exact CFSG.KD.Fi24ThreeO.invC_lt hf l hl
    · rw [e, lIf_true] at hl
      exact hf l hl

theorem letU_small {sl : List (ℕ × List ℕ × List ℕ)} {z : ℕ} (hz : z ≤ 5) : letU sl z = letU [] z := by
  unfold letU
  rw [ble_of hz, lIf_true, lIf_true]

theorem expU_lt {sl : List (ℕ × List ℕ × List ℕ)} (hsl : ∀ e ∈ sl, ∀ l ∈ e.2.2, l < 26) :
    ∀ (w : List ℕ), ∀ l ∈ expU sl w, l < 26
  | [], l, hl => absurd hl List.not_mem_nil
  | z :: w, l, hl => by
    change l ∈ letU sl z ++ expU sl w at hl
    rcases List.mem_append.1 hl with h | h
    · exact letU_lt hsl z l h
    · exact expU_lt hsl w l h

theorem wordElt_expU {sl : List (ℕ × List ℕ × List ℕ)} :
    ∀ (w : List ℕ), wordElt (expU sl w) = (w.map fun z => wordElt (letU sl z)).prod
  | [] => rfl
  | z :: w => by
    change wordElt (letU sl z ++ expU sl w) = _
    rw [wordElt_append, wordElt_expU w, List.map_cons, List.prod_cons]

theorem cb_mem {t : ℕ} (ht : t < 6) : CFSG.Sporadic.Fi24.Native.chainBase[t]! ∈ cb := by
  rw [chainBase_eq]
  interval_cases t <;> decide

theorem wordElt_eq_of_cb (hB : Bridge) {u v : List ℕ} (hu : ∀ l ∈ u, l < 26) (hv : ∀ l ∈ v, l < 26)
    (h : ∀ b ∈ cb, cP NW NT u b = cP NW NT v b) : wordElt u = wordElt v := by
  refine eq_of_base fun t ht => Fin.ext ?_
  rw [word_val hB _ hu, word_val hB _ hv]
  exact h _ (cb_mem ht)

theorem wordElt_eq_slpG (hB : Bridge) {sl : List (ℕ × List ℕ × List ℕ)}
    (h1 : ∀ e ∈ sl, (∀ z ∈ e.2.1, 2 ≤ z ∧ (z ≤ 5 ∨ (z / 2 - 3 < e.1 ∧ ∃ e' ∈ sl, e'.1 = z / 2 - 3))) ∧
      ∀ b ∈ cb, cP NW NT (expU sl e.2.1) b = cP NW NT e.2.2 b)
    (h2 : ∀ e ∈ sl, ∀ l ∈ e.2.2, l < 26)
    (h3 : ∀ e ∈ sl, e.1 < 1087 ∧ CFSG.KD.F24S.W7.getD e.1 [] = e.2.1) :
    ∀ e ∈ sl, wordElt e.2.2 = WG e.1 := by
  have key : ∀ n, ∀ e ∈ sl, e.1 = n → wordElt e.2.2 = WG n := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro e he hen
      obtain ⟨hz, hag⟩ := h1 e he
      obtain ⟨hn, hw⟩ := h3 e he
      rw [← wordElt_eq_of_cb hB (expU_lt h2 _) (h2 e he) hag, wordElt_expU,
        CFSG.Sporadic.Fi23.slpG_eq]
      have hwords : fi24SevenData.words[n]! = decW e.2.1 := by
        rw [CertificateChecks.KernelF24S.words_eq, ← hw, hen]
        rw [getElem!_pos _ n (by simp [CertificateChecks.KernelF24S.w7_len]; omega)]
        simp only [List.getElem_toArray, List.getElem_map]
        rw [List.getD_eq_getElem _ _ (by rw [CertificateChecks.KernelF24S.w7_len]; omega)]
      rw [hwords]
      unfold wordG decW
      rw [List.map_map]
      congr 1
      refine List.map_congr_left fun z hzm => ?_
      obtain ⟨hz2, hz'⟩ := hz z hzm
      simp only [Function.comp]
      have habs : (decC z).natAbs = z / 2 := by
        unfold decC
        split_ifs
        · rw [Int.natAbs_neg, Int.natAbs_natCast]
        · rw [Int.natAbs_natCast]
      by_cases h5 : z ≤ 5
      · rw [letU_small h5, genG_letter z hz2 h5, if_pos (by rw [habs]; omega)]
      · obtain ⟨hlt, e', he', he'k⟩ := hz'.resolve_left h5
        rw [hen] at hlt
        obtain ⟨e'', he'', he''k, hfu⟩ := findU_spec ⟨e', he', he'k⟩
        have hIH := ih _ hlt e'' he'' he''k
        rw [if_neg (by rw [habs]; omega), habs, if_pos hlt]
        unfold letU
        rw [ble_ne h5, lIf_false]
        have hsh : Nat.sub (Nat.shiftRight z 1) 3 = z / 2 - 3 := by
          simp [Nat.shiftRight_eq_div_pow]
        have hland : Nat.land z 1 = z % 2 := Nat.and_one_is_mod z
        rw [hsh, hfu, hland]
        by_cases hev : z % 2 = 0
        · have hd : decC z = ((z / 2 : ℕ) : ℤ) := by unfold decC; rw [if_neg (by omega)]
          rw [beq_of hev, lIf_true, hIH, if_pos (by rw [hd]; exact_mod_cast (by omega : 0 < z / 2))]
        · have hd : decC z = -((z / 2 : ℕ) : ℤ) := by unfold decC; rw [if_pos (by omega)]
          have hp : (0 : ℤ) < ((z / 2 : ℕ) : ℤ) := by exact_mod_cast (by omega : 0 < z / 2)
          rw [beq_ne hev, lIf_false, wordElt_invC hB (h2 e'' he''), hIH,
            if_neg (by rw [hd]; omega)]
  exact fun e he => key e.1 e he rfl

end CFSG.KD.Fi24Sev.Words

end
