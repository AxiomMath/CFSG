module

public import Certificates.Kernel.Sporadic.Fi24ThreeAK.Scan
public import Certificates.Kernel.Sporadic.Fi24ThreeAK.D4A
public import Certificates.Kernel.Sporadic.Fi24ThreeAK.D4B
public import Certificates.Kernel.Sporadic.Fi24Kit.Facts

public section

namespace CFSG.KD.Fi24ThreeAK

open CFSG.KC CFSG.KC.Fi24Kit CFSG.KC.Fi24ThreeAK CFSG.KS.Fi24Net CFSG.KS.Fi24Kit CFSG.KD.Fi24Net
  CFSG.KD.Fi24Kit

theorem line_fact : clsK CFSG.KD.Fi24Orb.OL NT 0 305530 = 73618 :=
  Nat.eq_of_beq_eq_true Ck.line_t

theorem ev_lt : ∀ l ∈ ev, l < 26 := by decide

theorem S0_testBit {y : Nat} (h : S0.testBit y = true) : y ∈ reps := by
  have hy : y < 14 := by
    by_contra hc
    have hlt : S0 < 2 ^ y :=
      lt_of_lt_of_le (by decide : (8238 : Nat) < 2 ^ 14) (Nat.pow_le_pow_right (by decide) (by omega))
    rw [Nat.testBit_lt_two_pow hlt] at h
    exact absurd h (by decide)
  revert h
  interval_cases y <;> decide

theorem F3_testBit {x : Nat} (h : F3.testBit x = true) : x = 0 ∨ x = 73618 ∨ x = 305530 := by
  change ((1 : Nat) ||| ((1 <<< 73618) ||| (1 <<< 305530))).testBit x = true at h
  rw [Nat.testBit_or, Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_shiftLeft] at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    Nat.testBit_one_eq_true_iff_self_eq_zero] at h
  omega

theorem cover_fact {x : Nat} (hx : x < 306936) (h0 : x ≠ 0) (h1 : x ≠ 73618) (h2 : x ≠ 305530) :
    ∃ w : List Nat, (∀ l ∈ w, l ∈ ev) ∧ wN NW w x ∈ reps := by
  rcases cover_spec (WV_of ev_lt) Ck.cov_t hx with h | ⟨w, hw, hS⟩
  · rcases F3_testBit h with h | h | h <;> contradiction
  · exact ⟨w, hw, S0_testBit hS⟩

theorem fl_all : ∀ i < 5, fl i = true := by
  intro i hi
  interval_cases i
  exacts [Ck.f0, Ck.f1, Ck.f2, Ck.f3, Ck.f4]

theorem fail_fact : ∀ i < 5,
    clsK CFSG.KD.Fi24Orb.OL NT (nthN reps i)
      (sK CFSG.KD.Fi24Orb.OL NT (clsK CFSG.KD.Fi24Orb.OL NT (nthN reps i) (nthN tests i))) ≠
      sKi CFSG.KD.Fi24Orb.OL NT (nthN tests i) :=
  fun i hi => fail_spec (fl_all i hi)

theorem d4_all : ∀ b < 6, d4 b = true := by
  intro b hb
  interval_cases b
  exacts [Ck.d0, Ck.d1, Ck.d2, Ck.d3, Ck.d4, Ck.d5]

theorem d4_fact {b : Nat} (hb : b < 6) :
    (∀ i ∈ [0, 1, 2, 3, 4, 5, 6, 7], wN NW (cube (W i)) (nthN base b) = nthN base b) ∧
    (∀ e ∈ [(0, 1), (1, 2), (1, 3)], (∀ w ∈ sixW W e.1 e.2, wN NW (cube w) (nthN base b) = nthN base b) ∧
      ∀ r ∈ rels, wN NW (relW (sixW W e.1 e.2) r) (nthN base b) = nthN base b) ∧
    (∀ e ∈ [(0, 2), (0, 3), (2, 3)], ∀ u ∈ [0, 1], ∀ v ∈ [0, 1],
      wN NW (W (2 * e.1 + u) ++ W (2 * e.2 + v)) (nthN base b) =
        wN NW (W (2 * e.2 + v) ++ W (2 * e.1 + u)) (nthN base b)) :=
  d4_spec (d4_all b hb)

theorem moves_fact : wN NW (W 0) 5604 ≠ 5604 ∧ wN NW (W 2) 5604 ≠ 5604 := by
  have h : andB (notB (Nat.beq (wP NW (W 0) 5604) 5604))
      (notB (Nat.beq (wP NW (W 2) 5604) 5604)) = true := Ck.mv_t
  rw [← wP_eq, ← wP_eq]
  refine ⟨fun e => ?_, fun e => ?_⟩
  · rw [e, Nat.beq_refl] at h
    generalize Nat.beq (wP NW (W 2) 5604) 5604 = c at h
    cases c <;> exact absurd h (by decide)
  · rw [e, Nat.beq_refl] at h
    generalize Nat.beq (wP NW (W 0) 5604) 5604 = c at h
    cases c <;> exact absurd h (by decide)

theorem fix_fact : ∀ i ∈ [0, 1, 2, 3, 4, 5, 6, 7], wN NW (W i) 0 = 0 ∧ wN NW (W i) 305530 = 305530 := by
  intro i hi
  obtain ⟨h1, h2⟩ := CFSG.KC.Benes.andB_true (allL_spec Ck.fix_t i hi)
  rw [← wP_eq, ← wP_eq]
  exact ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2⟩

theorem cj_all : ∀ b < 6, cj b = true := by
  intro b hb
  interval_cases b
  exacts [Ck.c0, Ck.c1, Ck.c2, Ck.c3, Ck.c4, Ck.c5]

theorem conj_fact {b : Nat} (hb : b < 6) :
    wN NW (cW ++ [18]) (nthN base b) = sK CFSG.KD.Fi24Orb.OL NT (wN NW cW (nthN base b)) :=
  conj_spec (cj_all b hb)

end CFSG.KD.Fi24ThreeAK

end
