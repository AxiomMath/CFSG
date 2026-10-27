
module

public import Certificates.Kernel.F4Syl3.PhiInvChk
public import CFSG.RankThree.PartTwo.Sec21.FF81F4Syl3Sound
public import CFSG.Certificates.Kernel.F4SaltSound
public import CFSG.RankThree.PartTwo.Sec21.FF81F4Elts
public import CFSG.RankThree.PartTwo.Sec21.FF81F4Gamma

public section

namespace CFSG.KC.F4Syl3

open CFSG.LieType.Simplicity.TitsBits CFSG.KC.F4Salt CFSG.KC.Loop
  CFSG.RankThree.PartTwo.Sec21.FF81.F4 CFSG.LieType.Ree
open CFSG.RankThree.PartOne.SEITZX (wordOfCodes letterOfCode)

theorem decW8_lt (W : ℕ) : ∀ L, ∀ c ∈ decW8 W L, c < 8
  | 0 => by simp [decW8]
  | L + 1 => by
    intro c hc
    rw [decW8, List.mem_append, List.mem_singleton] at hc
    rcases hc with hc | rfl
    · exact decW8_lt W L c hc
    · exact Nat.mod_lt _ (by decide)

theorem length_decW8 (W : ℕ) : ∀ L, (decW8 W L).length = L
  | 0 => rfl
  | L + 1 => by rw [decW8, List.length_append, length_decW8 W L, List.length_singleton]

theorem getElem_decW8 (W : ℕ) : ∀ (L m : ℕ) (h : m < (decW8 W L).length),
    (decW8 W L)[m] = digit W m
  | 0, m, h => absurd h (by simp [decW8])
  | L + 1, m, h => by
    rw [digit_eq]
    simp only [decW8]
    by_cases hm : m < L
    · rw [List.getElem_append_left (by rw [length_decW8]; exact hm), getElem_decW8 W L m _,
        digit_eq]
    · have hm' : m = L := by
        rw [length_decW8] at h
        omega
      subst hm'
      rw [List.getElem_append_right (by simp [length_decW8])]
      simp [length_decW8]

theorem allN_spec {n : ℕ} {p : ℕ → Bool} (h : allN n p = true) : ∀ m, m < n → p m = true := by
  induction n with
  | zero => intro m hm; omega
  | succ n ih =>
    simp only [allN, Bool.and_eq_true] at h
    intro m hm
    rcases Nat.lt_succ_iff_lt_or_eq.1 hm with hm | rfl
    · exact ih h.2 m hm
    · exact h.1

theorem decW8_of_flipOK {W Wf L : ℕ} (h : flipOK W Wf L = true) :
    decW8 Wf L = (decW8 W L).map flipC := by
  have h' := allN_spec h
  apply List.ext_getElem (by simp [length_decW8])
  intro m h1 h2
  rw [List.getElem_map, getElem_decW8, getElem_decW8]
  exact beq_iff_eq.1 (h' m (by rwa [length_decW8] at h1))

theorem decW8_of_revOK {W Wr L : ℕ} (h : revOK W Wr L = true) :
    decW8 Wr L = (decW8 W L).reverse := by
  have h' := allN_spec h
  apply List.ext_getElem (by simp [length_decW8])
  intro m h1 h2
  rw [List.getElem_reverse, getElem_decW8, getElem_decW8]
  rw [length_decW8] at h1
  rw [length_decW8]
  exact beq_iff_eq.1 (h' m h1)

theorem toNat_mul_eq_one {b : Bool} {n : ℕ} (h : b.toNat * n = 1) : b = true ∧ n = 1 := by
  cases b <;> simp_all

theorem toNat_eq_one {b : Bool} (h : b.toNat = 1) : b = true := by
  cases b <;> simp_all

noncomputable abbrev wE (W L : ℕ) : F42C := evalG (ZMod 2) (wordOfCodes (decW8 W L))

theorem hasBitsS_wE (W L : ℕ) : HasBitsS (ZMod 2) (wE W L) (wordS W L) := hasBitsS_wordS W L

theorem phi_link_F42 : IsConj (ReeTag.F4.finiteExceptionalAut (ZMod 2) rAE) rBE := by
  have h := CFSG.KD.F4Syl3.phi_ok
  simp only [phiN, strictN_eq] at h
  obtain ⟨hf, h⟩ := toNat_mul_eq_one h
  have h := toNat_eq_one h
  simp only [Bool.and_eq_true] at h
  obtain ⟨hA, hB⟩ := h
  have hf' : decW8 CFSG.KD.F4Syl3.waf CFSG.KD.F4Syl3.la =
      (decW8 CFSG.KD.F4Syl3.wa CFSG.KD.F4Syl3.la).map flipCode := decW8_of_flipOK hf
  have hrA : wE CFSG.KD.F4Syl3.wa CFSG.KD.F4Syl3.la = rAE :=
    ((hasBitsS_wE _ _).eq_iff (hasBitsS_saltOf hasBits_rAE)).2 hA
  have hflip : ReeTag.F4.finiteExceptionalAut (ZMod 2) (wE CFSG.KD.F4Syl3.wa CFSG.KD.F4Syl3.la) =
      wE CFSG.KD.F4Syl3.waf CFSG.KD.F4Syl3.la := by
    rw [wE, wE, hf', wordOfCodes_flip _ (decW8_lt _ _)]
    exact exceptionalAut_evalG _
  refine isConj_iff.2 ⟨wE CFSG.KD.F4Syl3.wb CFSG.KD.F4Syl3.lb, ?_⟩
  rw [← hrA, hflip]
  have e := (((hasBitsS_wE _ _).mul (hasBitsS_wE _ _)).eq_iff
    ((hasBitsS_saltOf hasBits_rBE).mul (hasBitsS_wE _ _))).2 hB
  rw [e, mul_inv_cancel_right]

theorem inv_of_invN {k W L Wr i j n : ℕ} (h : (invN k W L Wr == n) = true) (hn : n = 1)
    (hi : k / 2 = i) (hj : k % 2 = j) {t ρ : F42C} (ht : HasBitsS (ZMod 2) t (saltOf (invT i)))
    (hρ : HasBitsS (ZMod 2) ρ (saltOf (rhoBits j))) :
    ∃ c : F42C, c * ρ * c⁻¹ * t = t * (c * ρ * c⁻¹) := by
  subst hi hj hn
  have h := beq_iff_eq.1 h
  simp only [invN, strictN_eq] at h
  obtain ⟨hr, h⟩ := toNat_mul_eq_one h
  have h := toNat_eq_one h
  have hr' : decW8 Wr L = (decW8 W L).reverse := decW8_of_revOK hr
  have hinv : (wE W L)⁻¹ = wE Wr L := by
    rw [wE, wE, evalG_inv, hr', wordOfCodes, wordOfCodes, List.map_reverse]
  refine ⟨wE W L, ?_⟩
  have hx : HasBitsS (ZMod 2) (wE W L * ρ * (wE W L)⁻¹)
      (mulS (mulS (wordS W L) (saltOf (rhoBits (k % 2)))) (wordS Wr L)) := by
    rw [hinv]
    exact ((hasBitsS_wE _ _).mul hρ).mul (hasBitsS_wE _ _)
  exact ((hx.mul ht).eq_iff (ht.mul hx)).2 h

theorem inv_comm_F42 : ∀ t ∈ [tE, uE, tuE, vE], ∀ ρ ∈ [rAE, rBE],
    ∃ c : F42C, c * ρ * c⁻¹ * t = t * (c * ρ * c⁻¹) := by
  have eA : rhoBits 0 = rAB := by simp [rhoBits, rAB, sB, sBits, posPS, posPL, posNS, posNL, rb]
  have eB : rhoBits 1 = rBB := by
    simp [rhoBits, rBBits, rBB, sB, sBits, posPS, posPL, posNS, posNL, rb]
  have e0 : invT 0 = tB := by simp [invT, tB, rb]
  have e1 : invT 1 = uB := by simp [invT, uB, rb]
  have e2 : invT 2 = tuB := by simp [invT, tuB, rb]
  have e3 : invT 3 = vB := by simp [invT, vB, rb]
  have hA : HasBitsS (ZMod 2) rAE (saltOf (rhoBits 0)) := by
    rw [eA]
    exact hasBitsS_saltOf hasBits_rAE
  have hB : HasBitsS (ZMod 2) rBE (saltOf (rhoBits 1)) := by
    rw [eB]
    exact hasBitsS_saltOf hasBits_rBE
  have h0 : HasBitsS (ZMod 2) tE (saltOf (invT 0)) := by
    rw [e0]
    exact hasBitsS_saltOf hasBits_tE
  have h1 : HasBitsS (ZMod 2) uE (saltOf (invT 1)) := by
    rw [e1]
    exact hasBitsS_saltOf hasBits_uE
  have h2 : HasBitsS (ZMod 2) tuE (saltOf (invT 2)) := by
    rw [e2]
    exact hasBitsS_saltOf hasBits_tuE
  have h3 : HasBitsS (ZMod 2) vE (saltOf (invT 3)) := by
    rw [e3]
    exact hasBitsS_saltOf hasBits_vE
  intro t ht ρ hρ
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht hρ
  rcases ht with rfl | rfl | rfl | rfl <;> rcases hρ with rfl | rfl
  · exact inv_of_invN CFSG.KD.F4Syl3.ch799602inv.r0 rfl rfl rfl h0 hA
  · exact inv_of_invN CFSG.KD.F4Syl3.ch799602inv.r1 rfl rfl rfl h0 hB
  · exact inv_of_invN CFSG.KD.F4Syl3.ch799602inv.r2 rfl rfl rfl h1 hA
  · exact inv_of_invN CFSG.KD.F4Syl3.ch799602inv.r3 rfl rfl rfl h1 hB
  · exact inv_of_invN CFSG.KD.F4Syl3.ch799602inv.r4 rfl rfl rfl h2 hA
  · exact inv_of_invN CFSG.KD.F4Syl3.ch799602inv.r5 rfl rfl rfl h2 hB
  · exact inv_of_invN CFSG.KD.F4Syl3.ch799602inv.r6 rfl rfl rfl h3 hA
  · exact inv_of_invN CFSG.KD.F4Syl3.ch799602inv.r7 rfl rfl rfl h3 hB

end CFSG.KC.F4Syl3

end
