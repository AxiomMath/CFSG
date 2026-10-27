module

public import CFSG.Certificates.Kernel.FF81FormsSound
public import Certificates.Kernel.FF81Forms.Checks

public section

namespace CFSG.KD.FF81F

open Matrix CFSG.KC.FF81F CFSG.RankThree.PartTwo.Sec21.FF81.GL6

theorem lenK_eq (L : List Nat) : lenK L = L.length := by
  induction L with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih

theorem walk_sound (PK : List (Nat × Nat × Nat × Nat × List Nat)) (L : List Nat) :
    ∀ base i, walkK PK base L = true → i < L.length → okK PK (base + i) (L.getD i 0) = true := by
  induction L with
  | nil => intro _ _ _ hi; exact absurd hi (Nat.not_lt_zero _)
  | cons k L ih =>
    intro base i h hi
    change bAnd(okK PK base k, walkK PK (Nat.succ base) L) = true at h
    rw [bAnd_eq_true] at h
    cases i with
    | zero => exact h.1
    | succ i =>
      have := ih (Nat.succ base) i h.2 (by simpa using hi)
      rwa [show base + (i + 1) = Nat.succ base + i by omega]

theorem chunk (L : List Nat) (base : Nat) (h : walkK PK base L = true)
    (hl : Nat.beq (lenK L) 1024 = true) (n : Nat) (hlo : base ≤ n) (hhi : n < base + 1024) :
    ∃ k, okK PK n k = true := by
  have hlen : L.length = 1024 := by rw [← lenK_eq]; exact Nat.eq_of_beq_eq_true hl
  have := walk_sound PK L base (n - base) h (by omega)
  rw [show base + (n - base) = n by omega] at this
  exact ⟨_, this⟩

theorem cover (n : Nat) (hn : n < 32768) : ∃ k, okK PK n k = true := by
  by_cases h0 : n < 1024
  · exact chunk t0 0 ch799700_w0 ch799700_l0 n (by omega) h0
  by_cases h1 : n < 2048
  · exact chunk t1 1024 ch799700_w1 ch799700_l1 n (by omega) h1
  by_cases h2 : n < 3072
  · exact chunk t2 2048 ch799700_w2 ch799700_l2 n (by omega) h2
  by_cases h3 : n < 4096
  · exact chunk t3 3072 ch799700_w3 ch799700_l3 n (by omega) h3
  by_cases h4 : n < 5120
  · exact chunk t4 4096 ch799700_w4 ch799700_l4 n (by omega) h4
  by_cases h5 : n < 6144
  · exact chunk t5 5120 ch799700_w5 ch799700_l5 n (by omega) h5
  by_cases h6 : n < 7168
  · exact chunk t6 6144 ch799700_w6 ch799700_l6 n (by omega) h6
  by_cases h7 : n < 8192
  · exact chunk t7 7168 ch799700_w7 ch799700_l7 n (by omega) h7
  by_cases h8 : n < 9216
  · exact chunk t8 8192 ch799700_w8 ch799700_l8 n (by omega) h8
  by_cases h9 : n < 10240
  · exact chunk t9 9216 ch799700_w9 ch799700_l9 n (by omega) h9
  by_cases h10 : n < 11264
  · exact chunk t10 10240 ch799700_w10 ch799700_l10 n (by omega) h10
  by_cases h11 : n < 12288
  · exact chunk t11 11264 ch799700_w11 ch799700_l11 n (by omega) h11
  by_cases h12 : n < 13312
  · exact chunk t12 12288 ch799700_w12 ch799700_l12 n (by omega) h12
  by_cases h13 : n < 14336
  · exact chunk t13 13312 ch799700_w13 ch799700_l13 n (by omega) h13
  by_cases h14 : n < 15360
  · exact chunk t14 14336 ch799700_w14 ch799700_l14 n (by omega) h14
  by_cases h15 : n < 16384
  · exact chunk t15 15360 ch799700_w15 ch799700_l15 n (by omega) h15
  by_cases h16 : n < 17408
  · exact chunk t16 16384 ch799700_w16 ch799700_l16 n (by omega) h16
  by_cases h17 : n < 18432
  · exact chunk t17 17408 ch799700_w17 ch799700_l17 n (by omega) h17
  by_cases h18 : n < 19456
  · exact chunk t18 18432 ch799700_w18 ch799700_l18 n (by omega) h18
  by_cases h19 : n < 20480
  · exact chunk t19 19456 ch799700_w19 ch799700_l19 n (by omega) h19
  by_cases h20 : n < 21504
  · exact chunk t20 20480 ch799700_w20 ch799700_l20 n (by omega) h20
  by_cases h21 : n < 22528
  · exact chunk t21 21504 ch799700_w21 ch799700_l21 n (by omega) h21
  by_cases h22 : n < 23552
  · exact chunk t22 22528 ch799700_w22 ch799700_l22 n (by omega) h22
  by_cases h23 : n < 24576
  · exact chunk t23 23552 ch799700_w23 ch799700_l23 n (by omega) h23
  by_cases h24 : n < 25600
  · exact chunk t24 24576 ch799700_w24 ch799700_l24 n (by omega) h24
  by_cases h25 : n < 26624
  · exact chunk t25 25600 ch799700_w25 ch799700_l25 n (by omega) h25
  by_cases h26 : n < 27648
  · exact chunk t26 26624 ch799700_w26 ch799700_l26 n (by omega) h26
  by_cases h27 : n < 28672
  · exact chunk t27 27648 ch799700_w27 ch799700_l27 n (by omega) h27
  by_cases h28 : n < 29696
  · exact chunk t28 28672 ch799700_w28 ch799700_l28 n (by omega) h28
  by_cases h29 : n < 30720
  · exact chunk t29 29696 ch799700_w29 ch799700_l29 n (by omega) h29
  by_cases h30 : n < 31744
  · exact chunk t30 30720 ch799700_w30 ch799700_l30 n (by omega) h30
  exact chunk t31 31744 ch799700_w31 ch799700_l31 n (by omega) (by omega)

theorem lenP_eq (L : List (Nat × Nat × Nat × Nat × List Nat)) : lenP L = L.length := by
  induction L with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih

theorem colsAt_mem (L : List (Nat × Nat × Nat × Nat × List Nat)) :
    ∀ k, k < L.length → ∃ x ∈ L, colsAt L k = x.2.2.2.2 := by
  induction L with
  | nil => intro k hk; exact absurd hk (Nat.not_lt_zero _)
  | cons x L ih =>
    intro k hk
    cases k with
    | zero => exact ⟨x, List.mem_cons_self, rfl⟩
    | succ k =>
      obtain ⟨y, hy, e⟩ := ih k (by simpa using hk)
      exact ⟨y, List.mem_cons_of_mem _ hy, e⟩

theorem allPairs_mem (L : List (Nat × Nat × Nat × Nat × List Nat)) (h : allPairs L = true) :
    ∀ x ∈ L, pairOK x = true := by
  induction L with
  | nil => intro x hx; exact absurd hx List.not_mem_nil
  | cons y L ih =>
    change bAnd(pairOK y, allPairs L) = true at h
    rw [bAnd_eq_true] at h
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h.1
    · exact ih h.2 x hx

theorem add_eq_zero_two {A B : Matrix (Fin 6) (Fin 6) (ZMod 2)} (h : A + B = 0) : A = B := by
  ext i j
  have e := congrFun (congrFun h i) j
  simp only [Matrix.add_apply, Matrix.zero_apply] at e
  generalize A i j = a at e
  generalize B i j = b at e
  revert a b
  decide

theorem forms_witness : ∀ P : Matrix (Fin 6) (Fin 6) (ZMod 2), Pᵀ = P → (∀ i, P i i = 0) →
    P ≠ J0 → ∃ s w : G6, s ∈ Sp0 ∧ w * u0 = u0 * w ∧ w ∉ Sp0 ∧
      (w : Matrix (Fin 6) (Fin 6) (ZMod 2))ᵀ *
          ((s : Matrix (Fin 6) (Fin 6) (ZMod 2))ᵀ * P * (s : Matrix (Fin 6) (Fin 6) (ZMod 2))) *
          (w : Matrix (Fin 6) (Fin 6) (ZMod 2)) =
        (s : Matrix (Fin 6) (Fin 6) (ZMod 2))ᵀ * P * (s : Matrix (Fin 6) (Fin 6) (ZMod 2)) := by
  intro P hsym hdiag hne
  have hsP : ∀ i j, P j i = P i j := fun i j => by
    simpa only [Matrix.transpose_apply] using congr_fun (congr_fun hsym i) j
  obtain ⟨n, hn, hP⟩ := exists_index P hsP hdiag
  have hn2 : Nat.beq n 2180 = false := by
    cases h : Nat.beq n 2180
    · rfl
    · exact absurd (by rw [← hP, Nat.eq_of_beq_eq_true h, linK_ES_J0]) hne
  obtain ⟨k, hk⟩ := cover n hn
  change bIf(Nat.beq n 2180, true, bAnd(Nat.blt k (lenP PK),
    Nat.beq (linK (colsAt PK k) n) 0)) = true at hk
  rw [hn2] at hk
  change bAnd(Nat.blt k (lenP PK), Nat.beq (linK (colsAt PK k) n) 0) = true at hk
  rw [bAnd_eq_true, lenP_eq] at hk
  obtain ⟨x, hx, hcx⟩ := colsAt_mem PK k (by simpa [Nat.blt_eq] using hk.1)
  obtain ⟨s, w, hs, hw, hsS, hwu, hwS, hcols⟩ := pair_sound x (allPairs_mem PK ch799700_pairs x hx)
  refine ⟨s, w, hsS, hwu, hwS, ?_⟩
  have e := decK_linK_cols _ _ _ _ n hcols
  rw [← hcx, Nat.eq_of_beq_eq_true hk.2, decK_zero, hP] at e
  rw [hs, hw]
  exact add_eq_zero_two e.symm

end CFSG.KD.FF81F
