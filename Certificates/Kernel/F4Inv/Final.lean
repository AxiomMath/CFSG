module

public import Certificates.Kernel.F4Inv.Rank
public import Certificates.Kernel.F4Inv.Comm
public import Certificates.Kernel.F4Inv.Long
public import Certificates.Kernel.F4Syl3.PhiInv
public import CFSG.Certificates.Kernel.F4Inv.Parabolic
public import CFSG.Certificates.Kernel.F4RankSound
import all CFSG.LieType.Simplicity.TitsBits
public import CFSG.RankThree.PartTwo.Sec21.FF81F4CenCard

public section

namespace CFSG.KC.F4Inv

open CFSG.RankThree.PartTwo.Sec21.FF81.F4 CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Ree CFSG.LieType.Simplicity.TitsBits CFSG.KC.F4Salt CFSG.KC.Loop CFSG.KC.F4Syl3
  CFSG.KC.F4Rank CFSG.ComponentClassification.RankTwoExceptional.F4Sec8 Module
open CFSG.RankThree.PartOne.SEITZX (wordOfCodes letterOfCode)


theorem weylElement_eq_letter (i : Fin 4) :
    weylElement ReeTag.F4.tag (ZMod 2) i = (letterOfCode (i + 4)).elt (ZMod 2) := by
  have h4 : ¬ ((i : ℕ) + 4 < 4) := by omega
  simp only [letterOfCode, h4, dite_false, Letter.elt]
  have h5 : (idx (⟨((i : ℕ) + 4 - 4) % 4, Nat.mod_lt _ (by norm_num)⟩ : Fin 4)) = i :=
    Fin.ext (by change ((i : ℕ) + 4 - 4) % 4 = i; omega)
  rw [h5]

theorem comm_iff_commN {x : F42C} {X : ℕ} (hx : HasBits (ZMod 2) x X) (i : Fin 4) :
    weylElement ReeTag.F4.tag (ZMod 2) i * x = x * weylElement ReeTag.F4.tag (ZMod 2) i ↔
      commN X (i + 4) = 1 := by
  rw [weylElement_eq_letter, ((hasBitsS_letS _).mul (hasBitsS_saltOf hx)).eq_iff
    ((hasBitsS_saltOf hx).mul (hasBitsS_letS _))]
  simp only [commN, strictN_eq]
  cases eqS (mulS (letS (i + 4)) (saltOf X)) (mulS (saltOf X) (letS (i + 4))) <;> simp

theorem commN_of_allN {X : ℕ} {f : ℕ → ℕ} (h : allN 4 (fun i => commN X (i + 4) == f i) = true)
    (i : ℕ) (hi : i < 4) : commN X (i + 4) = f i :=
  beq_iff_eq.1 (allN_spec h i hi)

theorem tE_central (q : F42C) (hq : q ∈ Q₀) : q * tE = tE * q := zB'_central hq

theorem tuE_eq : tuE = zA * zB' :=
  (f4Rep_pair (K := ZMod 2) 47 44).trans (zA_central zB'_mem)

theorem tuE_central (q : F42C) (hq : q ∈ Q₀) : q * tuE = tuE * q := by
  rw [tuE_eq, ← mul_assoc, zA_central hq, mul_assoc, zB'_central hq, mul_assoc]

theorem invT_zero : invT 0 = tB := by simp [invT, tB, rb]

theorem invT_two : invT 2 = tuB := by simp [invT, tuB, rb]

theorem cen_tE : cenGL tE = parabolicSubgroup ReeTag.F4.tag (ZMod 2) {i | i ≠ 0} := by
  rw [cen_eq_parabolic tE_central]
  congr 1
  ext i
  rw [Set.mem_setOf_eq, Set.mem_setOf_eq]
  refine (comm_iff_commN (invT_zero ▸ hasBits_tE) i).trans ?_
  rw [commN_of_allN CFSG.KD.F4Inv.comm_t _ i.2]
  fin_cases i <;> decide

theorem cen_tuE : cenGL tuE = parabolicSubgroup ReeTag.F4.tag (ZMod 2) {i | i ≠ 0 ∧ i ≠ 3} := by
  rw [cen_eq_parabolic tuE_central]
  congr 1
  ext i
  rw [Set.mem_setOf_eq, Set.mem_setOf_eq]
  refine (comm_iff_commN (invT_two ▸ hasBits_tuE) i).trans ?_
  rw [commN_of_allN CFSG.KD.F4Inv.comm_tu _ i.2]
  fin_cases i <;> decide

theorem card_cen_tE' : Nat.card (Subgroup.centralizer ({tE} : Set F42C)) = 2 ^ 24 * 3 ^ 4 * 5 * 7 := by
  rw [← card_cenGL, cen_tE, card_parabolic_123]

theorem card_cen_tuE_lt :
    Nat.card (Subgroup.centralizer ({tuE} : Set F42C)) < 2 ^ 24 * 3 ^ 4 * 5 * 7 := by
  rw [← card_cenGL, cen_tuE, ← card_parabolic_123]
  exact card_parabolic_12_lt

theorem classes_of_cen' (x : F42C) (hx : orderOf x = 2)
    (hc : Nat.card (Subgroup.centralizer ({x} : Set F42C)) = 2 ^ 24 * 3 ^ 4 * 5 * 7) :
    IsConj tE x ∨ IsConj uE x := by
  rcases conj_center_of_card_cen hx hc with h | h | h
  · exact Or.inr h
  · exact Or.inl h
  · rw [← tuE_eq] at h
    have h1 := card_cen_isConj h
    have h2 := card_cen_tuE_lt
    rw [h1, hc] at h2
    exact absurd h2 (lt_irrefl _)

theorem long_of_row {W L a n : ℕ} (h : (longN W L a == n) = true) (hn : n = 1) {b : ℕ}
    (hab : a = b) {y : F42C} (hy : HasBits (ZMod 2) y (rb b)) : IsConj tE y := by
  subst hab hn
  have h := beq_iff_eq.1 h
  simp only [longN, strictN_eq] at h
  have h' := toNat_eq_one h
  refine isConj_iff.2 ⟨wE W L, ?_⟩
  have e := (((hasBitsS_wE W L).mul (hasBitsS_saltOf (invT_zero ▸ hasBits_tE))).eq_iff
    ((hasBitsS_saltOf hy).mul (hasBitsS_wE W L))).2 h'
  rw [e, mul_inv_cancel_right]

theorem long_conj_row : ∀ j < 12, ∀ {y : F42C},
    HasBits (ZMod 2) y (rb (CFSG.KC.F4Inv.longPos.getD j 0)) → IsConj tE y
  | 0, _, _, hy => long_of_row CFSG.KD.F4Inv.ch799601long.r0 rfl rfl hy
  | 1, _, _, hy => long_of_row CFSG.KD.F4Inv.ch799601long.r1 rfl rfl hy
  | 2, _, _, hy => long_of_row CFSG.KD.F4Inv.ch799601long.r2 rfl rfl hy
  | 3, _, _, hy => long_of_row CFSG.KD.F4Inv.ch799601long.r3 rfl rfl hy
  | 4, _, _, hy => long_of_row CFSG.KD.F4Inv.ch799601long.r4 rfl rfl hy
  | 5, _, _, hy => long_of_row CFSG.KD.F4Inv.ch799601long.r5 rfl rfl hy
  | 6, _, _, hy => long_of_row CFSG.KD.F4Inv.ch799601long.r6 rfl rfl hy
  | 7, _, _, hy => long_of_row CFSG.KD.F4Inv.ch799601long.r7 rfl rfl hy
  | 8, _, _, hy => long_of_row CFSG.KD.F4Inv.ch799601long.r8 rfl rfl hy
  | 9, _, _, hy => long_of_row CFSG.KD.F4Inv.ch799601long.r9 rfl rfl hy
  | 10, _, _, hy => long_of_row CFSG.KD.F4Inv.ch799601long.r10 rfl rfl hy
  | 11, _, _, hy => long_of_row CFSG.KD.F4Inv.ch799601long.r11 rfl rfl hy
  | n + 12, h, _, _ => absurd h (by omega)

theorem longPair_row : ∀ k : Fin 12, ∃ j < 12,
    certPos (f4PairLong k) = CFSG.KC.F4Inv.longPos.getD j 0 ∧ 24 ≤ f4PairLong k ∧
      f4PairLong k ≤ 47 := by
  decide

theorem long_conj (k : Fin 12) : IsConj tE (f4Rep (ZMod 2) [f4PairLong k]) := by
  obtain ⟨j, hj, he, h1, h2⟩ := longPair_row k
  have hb := hasBits_f4Rep_single (K := ZMod 2) (f4PairLong k) ⟨h1, h2⟩
  rw [he] at hb
  exact long_conj_row j hj hb

noncomputable abbrev endo (x : F42C) : Module.End (ZMod 2) (RootModule ReeTag.F4.tag (ZMod 2)) :=
  ((x : ModGL ReeTag.F4.tag (ZMod 2)) : Module.End (ZMod 2) (RootModule ReeTag.F4.tag (ZMod 2)))

theorem sBits_three : sBits 3 = rAB := by
  simp [sBits, rAB, CFSG.RankThree.PartTwo.Sec21.FF81.F4.sB, posPS, posPL, posNS, posNL, rb]

theorem rBBits_eq : rBBits = rBB := by
  simp [rBBits, rBB, CFSG.RankThree.PartTwo.Sec21.FF81.F4.sB, sBits, posPS, posPL, posNS, posNL, rb]

theorem zBits_eq : CFSG.KD.F4Inv.zBits = zB := by
  simp [CFSG.KD.F4Inv.zBits, zB, sqB, CFSG.RankThree.PartTwo.Sec21.FF81.F4.sB, sBits, posPS, posPL, posNS, posNL, rb]

theorem u26_invariant (c : F42C) :
    (coordSub (ZMod 2) CFSG.KD.F4Inv.u26).map (endo c) = coordSub (ZMod 2) CFSG.KD.F4Inv.u26 := by
  have hS : ∀ s ∈ gL (ZMod 2) '' {k | k < letterGB.size}, ∃ A, HasBits (ZMod 2) s A ∧
      stabChk CFSG.KD.F4Inv.u26 A = true := by
    rintro _ ⟨l, hl, rfl⟩
    have hl8 : l < 8 := by rwa [letterGB_size] at hl
    have e : letterGB[l]! = (letterOfCode l).bits := by
      rw [getElem!_pos letterGB l hl]
      simp [letterGB, hl8]
    refine ⟨(letterOfCode l).bits, ?_, allN_spec CFSG.KD.F4Inv.stab_ok l hl8⟩
    rw [← e]
    exact gL_bits l hl
  refine map_coordSub_closure hS c ?_
  rw [gL_gen (by simp)]
  exact Subgroup.mem_top c

theorem card_u26 : Fintype.card {p : Fin 52 // CFSG.KD.F4Inv.u26.testBit p = true} = 26 := by
  decide +kernel

theorem rho_not_conj : ¬IsConj rAE rBE ∧ ¬IsConj rAE zE ∧ ¬IsConj rBE zE := by
  have eA : endo rAE = toEnd (ZMod 2) rAB := hasBits_rAE
  have eB : endo rBE = toEnd (ZMod 2) rBB := hasBits_rBE
  have eZ : endo zE = toEnd (ZMod 2) zB := hasBits_zE
  have hA : 22 ≤ finrank (ZMod 2) ↥(LinearMap.ker (endo rAE - 1)) := by
    have h := fixChk_sound (K := ZMod 2) CFSG.KD.F4Inv.kRA_ok
    rw [sBits_three, ← eA] at h
    exact h
  have hB : 22 ≤ finrank (ZMod 2) ↥(LinearMap.ker (endo rBE - 1)) := by
    have h := fixChk_sound (K := ZMod 2) CFSG.KD.F4Inv.kRB_ok
    rw [rBBits_eq, ← eB] at h
    exact h
  have hZ : finrank (ZMod 2) ↥(LinearMap.ker (endo zE - 1)) ≤ 16 := by
    have h := rankChk_sound (K := ZMod 2) CFSG.KD.F4Inv.iZ_ok
    rw [zBits_eq, ← eZ] at h
    have h2 := finrank_range_add_finrank_ker_F4 (K := ZMod 2) (endo zE - 1)
    have hl : CFSG.KD.F4Inv.iZ.length = 36 := by decide +kernel
    omega
  have hAU : 14 ≤ finrank (ZMod 2) ↥(LinearMap.ker (endo rAE - 1) ⊓
      coordSub (ZMod 2) CFSG.KD.F4Inv.u26) := by
    have h := fixSubChk_sound (K := ZMod 2) CFSG.KD.F4Inv.kRAU_ok
    rw [sBits_three, ← eA] at h
    exact h
  have hBU : finrank (ZMod 2) ↥(LinearMap.ker (endo rBE - 1) ⊓
      coordSub (ZMod 2) CFSG.KD.F4Inv.u26) ≤ 8 := by
    have h := rankSubChk_sound (K := ZMod 2) CFSG.KD.F4Inv.iRBU_ok
    rw [rBBits_eq, ← eB] at h
    have h2 := finrank_map_add_finrank_ker_inf (endo rBE - 1) (coordSub (ZMod 2) CFSG.KD.F4Inv.u26)
    have h3 := finrank_coordSub_le (K := ZMod 2) CFSG.KD.F4Inv.u26
    rw [card_u26] at h3
    have hl : CFSG.KD.F4Inv.iRBU.length = 18 := by decide +kernel
    omega
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have e : finrank (ZMod 2) ↥(LinearMap.ker (endo rAE - 1) ⊓
        coordSub (ZMod 2) CFSG.KD.F4Inv.u26) = finrank (ZMod 2) ↥(LinearMap.ker (endo rBE - 1) ⊓
        coordSub (ZMod 2) CFSG.KD.F4Inv.u26) := finrank_ker_inf_eq_of_isConj u26_invariant h
    omega
  · have e : finrank (ZMod 2) ↥(LinearMap.ker (endo rAE - 1)) =
        finrank (ZMod 2) ↥(LinearMap.ker (endo zE - 1)) := finrank_ker_eq_of_isConj h
    omega
  · have e : finrank (ZMod 2) ↥(LinearMap.ker (endo rBE - 1)) =
        finrank (ZMod 2) ↥(LinearMap.ker (endo zE - 1)) := finrank_ker_eq_of_isConj h
    omega

theorem inv_facts_F42 :
    Nat.card (Subgroup.centralizer ({tE} : Set F42C)) = 2 ^ 24 * 3 ^ 4 * 5 * 7 ∧
    (∀ k : Fin 12, IsConj tE (f4Rep (ZMod 2) [f4PairLong k])) ∧
    (∀ x : F42C, orderOf x = 2 →
      Nat.card (Subgroup.centralizer ({x} : Set F42C)) = 2 ^ 24 * 3 ^ 4 * 5 * 7 →
        IsConj tE x ∨ IsConj uE x) ∧
    (¬IsConj rAE rBE ∧ ¬IsConj rAE zE ∧ ¬IsConj rBE zE) :=
  ⟨card_cen_tE', long_conj, classes_of_cen', rho_not_conj⟩

end CFSG.KC.F4Inv

end
