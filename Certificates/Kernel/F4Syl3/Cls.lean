module

public import Certificates.Kernel.F4Syl3.ClsChk
public import Certificates.Kernel.F4Syl3.PhiInv
public import CFSG.Certificates.Kernel.F4Syl3.ModelUse
public import Certificates.Kernel.F4Syl3.Pres

public section

namespace CFSG.KC.F4Syl3

open CFSG.LieType.Simplicity.TitsBits CFSG.KC.F4Salt CFSG.KC.Loop
  CFSG.RankThree.PartTwo.Sec21.FF81.F4 CFSG.KD.F4Syl3
open CFSG.RankThree.PartOne.SEITZX (wordOfCodes letterOfCode)


noncomputable abbrev trgE (t : ℕ) : F42C := if t = 0 then rAE else if t = 1 then rBE else zE

noncomputable abbrev SS : List ℕ :=
  [saltOf (pS.getD 0 0), saltOf (pS.getD 1 0), saltOf (pS.getD 2 0), saltOf (pS.getD 3 0)]

theorem pins : sBits 0 = pS.getD 0 0 ∧ sBits 1 = pS.getD 1 0 ∧ sBits 2 = pS.getD 2 0 ∧
    sBits 3 = pS.getD 3 0 ∧ wordS w4 l4 = saltOf (pS.getD 4 0) ∧
    wordS w5 l5 = saltOf (pS.getD 5 0) := by
  have h := pin_ok
  simp only [pinB, Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h0, h1, h2, h3, h4, h5⟩

theorem hasBitsS_SS (i : Fin 4) : HasBitsS (ZMod 2) (sE i) (SS.getD i 0) := by
  obtain ⟨h0, h1, h2, h3, -⟩ := pins
  rcases i with ⟨_ | _ | _ | _ | n, hi⟩
  · simp only [Fin.val_mk, List.getD_cons_zero]
    rw [← h0]
    exact hasBitsS_sE _
  · simp only [Fin.val_mk, Nat.zero_add, List.getD_cons_succ, List.getD_cons_zero]
    rw [← h1]
    exact hasBitsS_sE _
  · simp only [Fin.val_mk, Nat.zero_add, List.getD_cons_succ, List.getD_cons_zero]
    rw [← h2]
    exact hasBitsS_sE _
  · simp only [Fin.val_mk, Nat.zero_add, List.getD_cons_succ, List.getD_cons_zero]
    rw [← h3]
    exact hasBitsS_sE _
  · omega

theorem hasBitsS_G4 : HasBitsS (ZMod 2) g4E (saltOf (pS.getD 4 0)) := by
  rw [← pins.2.2.2.2.1]
  exact hasBitsS_wordS _ _

theorem hasBitsS_G5 : HasBitsS (ZMod 2) g5E (saltOf (pS.getD 5 0)) := by
  rw [← pins.2.2.2.2.2]
  exact hasBitsS_wordS _ _

theorem hasBitsS_phiS (m : ℕ) : HasBitsS (ZMod 2) (phi sE g4E g5E m)
    (phiS SS (saltOf (pS.getD 4 0)) (saltOf (pS.getD 5 0)) m) :=
  (hasBitsS_fSS hasBitsS_SS _).mul
    ((hasBitsS_powS hasBitsS_G4 _).mul (hasBitsS_powS hasBitsS_G5 _))

theorem hasBitsS_tgtS (t : ℕ) : HasBitsS (ZMod 2) (trgE t) (tgtS SS t) := by
  have s : ∀ i : Fin 4, HasBitsS (ZMod 2) (sE i) (SS.getD i 0) := hasBitsS_SS
  by_cases h0 : t = 0
  · simp only [trgE, tgtS, h0, if_true]
    exact s 3
  by_cases h1 : t = 1
  · simp only [trgE, tgtS, h1, if_true, one_ne_zero, if_false]
    exact (s 0).mul (s 1)
  simp only [trgE, tgtS, h0, h1, if_false]
  exact (((s 0).mul (s 0)).mul ((s 1).mul (s 1))).mul ((s 2).mul (s 2))

theorem isConj_of_mul {x y c : F42C} (h : c * x = y * c) : IsConj x y :=
  isConj_iff.2 ⟨c, by rw [h, mul_inv_cancel_right]⟩

theorem row_sound {k n : ℕ} (h : (clsRowN pS tgt cpar clet ca cb cw cl k == n) = true)
    (hn : n = 1) {j : ℕ} (hj : k = j) : IsConj (phi sE g4E g5E (ca.getD j 0))
      (if cpar.getD j 0 = 48 then trgE (tgt.getD j 3) else phi sE g4E g5E (cb.getD j 0)) := by
  subst hn hj
  have h := beq_iff_eq.1 h
  simp only [clsRowN, strictN_eq] at h
  by_cases hr : cpar.getD k 0 = 48
  · rw [if_pos hr] at h ⊢
    have e := toNat_eq_one h
    exact isConj_of_mul ((((hasBitsS_wordS _ _).mul (hasBitsS_phiS _)).eq_iff
      ((hasBitsS_tgtS _).mul (hasBitsS_wordS _ _))).2 e)
  · rw [if_neg hr] at h ⊢
    have e := toNat_eq_one h
    exact isConj_of_mul ((((hasBitsS_letS _).mul (hasBitsS_phiS _)).eq_iff
      ((hasBitsS_phiS _).mul (hasBitsS_letS _))).2 e)

theorem rows_sound : ∀ k, k < 48 → IsConj (phi sE g4E g5E (ca.getD k 0))
    (if cpar.getD k 0 = 48 then trgE (tgt.getD k 3) else phi sE g4E g5E (cb.getD k 0)) := by
  intro k hk
  interval_cases k
  exacts [row_sound ch799602cls.r0 rfl rfl, row_sound ch799602cls.r1 rfl rfl,
    row_sound ch799602cls.r2 rfl rfl, row_sound ch799602cls.r3 rfl rfl, row_sound ch799602cls.r4 rfl rfl,
    row_sound ch799602cls.r5 rfl rfl, row_sound ch799602cls.r6 rfl rfl, row_sound ch799602cls.r7 rfl rfl,
    row_sound ch799602cls.r8 rfl rfl, row_sound ch799602cls.r9 rfl rfl, row_sound ch799602cls.r10 rfl rfl,
    row_sound ch799602cls.r11 rfl rfl, row_sound ch799602cls.r12 rfl rfl, row_sound ch799602cls.r13 rfl rfl,
    row_sound ch799602cls.r14 rfl rfl, row_sound ch799602cls.r15 rfl rfl, row_sound ch799602cls.r16 rfl rfl,
    row_sound ch799602cls.r17 rfl rfl, row_sound ch799602cls.r18 rfl rfl, row_sound ch799602cls.r19 rfl rfl,
    row_sound ch799602cls.r20 rfl rfl, row_sound ch799602cls.r21 rfl rfl, row_sound ch799602cls.r22 rfl rfl,
    row_sound ch799602cls.r23 rfl rfl, row_sound ch799602cls.r24 rfl rfl, row_sound ch799602cls.r25 rfl rfl,
    row_sound ch799602cls.r26 rfl rfl, row_sound ch799602cls.r27 rfl rfl, row_sound ch799602cls.r28 rfl rfl,
    row_sound ch799602cls.r29 rfl rfl, row_sound ch799602cls.r30 rfl rfl, row_sound ch799602cls.r31 rfl rfl,
    row_sound ch799602cls.r32 rfl rfl, row_sound ch799602cls.r33 rfl rfl, row_sound ch799602cls.r34 rfl rfl,
    row_sound ch799602cls.r35 rfl rfl, row_sound ch799602cls.r36 rfl rfl, row_sound ch799602cls.r37 rfl rfl,
    row_sound ch799602cls.r38 rfl rfl, row_sound ch799602cls.r39 rfl rfl, row_sound ch799602cls.r40 rfl rfl,
    row_sound ch799602cls.r41 rfl rfl, row_sound ch799602cls.r42 rfl rfl, row_sound ch799602cls.r43 rfl rfl,
    row_sound ch799602cls.r44 rfl rfl, row_sound ch799602cls.r45 rfl rfl, row_sound ch799602cls.r46 rfl rfl,
    row_sound ch799602cls.r47 rfl rfl]

theorem conj_code {m : ℕ} (h : ord3 m = true) :
    clsOf cover m < 48 ∧
      IsConj (phi sE g4E g5E m) (phi sE g4E g5E (reps.getD (clsOf cover m) 0)) := by
  simp only [ord3, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, beq_iff_eq] at h
  obtain ⟨⟨hm, h0⟩, h3⟩ := h
  obtain ⟨hk, he⟩ := cover_spec cover_ok hm h0 h3
  refine ⟨hk, isConj_iff.2 ⟨phi sE g4E g5E (cover.getD m (0, 0)).1, ?_⟩⟩
  rw [clsOf, ← phi_pmul pres_F42, he, phi_pmul pres_F42, mul_inv_cancel_right]

theorem rep_conj : ∀ k, k < 48 →
    IsConj (phi sE g4E g5E (reps.getD k 0)) (trgE (tgt.getD k 3)) := by
  have hM := allB_spec cls_model_ok
  suffices H : ∀ n k, k < 48 → cdep.getD k 0 ≤ n →
      IsConj (phi sE g4E g5E (reps.getD k 0)) (trgE (tgt.getD k 3)) from
    fun k hk => H _ k hk le_rfl
  intro n
  induction n with
  | zero => ?_
  | succ n ih => ?_
  all_goals
    intro k hk hd
    have hk' := hM k hk
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hk'
    obtain ⟨⟨ha, hca⟩, hpar⟩ := hk'
    obtain ⟨-, hA⟩ := conj_code ha
    rw [hca] at hA
    have hrow := rows_sound k hk
    rcases hpar with hr | ⟨⟨⟨⟨hp, hb⟩, hcb⟩, ht⟩, hdp⟩
    · rw [if_pos hr] at hrow
      exact hA.symm.trans hrow
    · have hne : cpar.getD k 0 ≠ 48 := by omega
      rw [if_neg hne] at hrow
      obtain ⟨-, hB⟩ := conj_code hb
      rw [hcb] at hB
      first
      | omega
      | have hP := ih _ hp (by omega)
        rw [ht] at hP
        exact hA.symm.trans (hrow.trans (hB.trans hP))

end CFSG.KC.F4Syl3

end
