module

public import Certificates.Kernel.MonsterB.Coset3023Sound

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CertificateChecks.Coset3023

open CFSG.KC.KDense CFSG.KLie.CT CFSG.Monster.B CFSG.KC.SortTree
  CFSG.Monster.B.TwoA.Census

theorem sumN_eq (n : ℕ) (f : ℕ → ℕ) : sumN n f = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change f n + sumN n f = _
    rw [ih, Finset.sum_range_succ, Nat.add_comm]

theorem jF_lt (J : ℕ → ℕ) (j o w : ℕ) : jF J j o w < 2 ^ w := by
  unfold jF maskN pw2
  change (recT J 6 50 j >>> o) &&& ((1 <<< w) - 1) < 2 ^ w
  rw [Nat.one_shiftLeft, Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_lt _ (by positivity)

theorem sum_blocks (f : ℕ → ℕ) (n : ℕ) : ∀ m,
    ∑ x ∈ Finset.range (n * m), f x = ∑ k ∈ Finset.range m, ∑ i ∈ Finset.range n, f (n * k + i)
  | 0 => by simp
  | m + 1 => by
    rw [Nat.mul_succ, Finset.sum_range_add, sum_blocks f n m, Finset.sum_range_succ]

theorem mono_of_succ {K : ℕ → ℕ} {N : ℕ} (h : ∀ j, j + 1 < N → K j ≤ K (j + 1)) :
    ∀ i j, i ≤ j → j < N → K i ≤ K j := by
  intro i j hij hj
  induction j with
  | zero => rw [Nat.le_zero.1 hij]
  | succ j ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le hij) with h' | h'
    · exact le_trans (ih (by omega) (by omega)) (h j hj)
    · rw [h']

theorem block_sum {TT : ℕ → ℕ} {w : Model.Pauli} {J : ℕ → ℕ} (hs : sortOK TT J = true) {a : ℕ}
    (hb : blockOK TT w J a = true) :
    ∑ d ∈ Finset.range 4096, (if kA TT w a = kD TT d then hW TT w a d else 0) =
      blockSum TT w J a := by
  rw [sortOK, andB_iff, allN_iff', allN_iff'] at hs
  obtain ⟨hp, hm⟩ := hs
  have hpi : ∀ j, jpi J j < 4096 := fun j => jF_lt J j 0 12
  have hrho : ∀ j, jrho J j < 4096 := fun j => jF_lt J j 12 12
  have hp' : ∀ d < 4096, jpi J (jrho J d) = d ∧ jrho J (jpi J d) = d := fun d hd => by
    have := hp d hd
    rw [andB_iff, Nat.beq_eq, Nat.beq_eq] at this
    exact this
  have hmono := mono_of_succ (K := fun j => kD TT (jpi J j)) (N := 4096) fun j hj => by
    have := hm j (by omega)
    rwa [Nat.ble_eq] at this
  have e1 : ∑ d ∈ Finset.range 4096, (if kA TT w a = kD TT d then hW TT w a d else 0) =
      ∑ j ∈ Finset.range 4096,
        (if kA TT w a = kD TT (jpi J j) then hW TT w a (jpi J j) else 0) := by
    refine (Finset.sum_nbij' (jpi J) (jrho J) (fun j _ => Finset.mem_range.2 (hpi j))
      (fun d _ => Finset.mem_range.2 (hrho d)) (fun j hj => (hp' j (Finset.mem_range.1 hj)).2)
      (fun d hd => (hp' d (Finset.mem_range.1 hd)).1) fun _ _ => rfl).symm
  rw [e1]
  clear e1
  unfold blockSum
  rw [sumN_eq]
  unfold blockOK at hb
  dsimp only at hb
  rw [andB_iff, andB_iff, andB_iff, allN_iff', Nat.ble_eq] at hb
  obtain ⟨hle, heq, hlo, hhi⟩ := hb
  generalize kA TT w a = k at heq hlo hhi ⊢
  generalize jlo J a = lo at hle heq hlo hhi ⊢
  change lo + jn J a ≤ 4096 at hle
  have hlo' : lo = 0 ∨ kD TT (jpi J (lo - 1)) < k := by
    cases h : Nat.beq lo 0
    · rw [h] at hlo
      change Nat.blt _ _ = true at hlo
      rw [Nat.blt_eq] at hlo
      exact Or.inr hlo
    · exact Or.inl (Nat.eq_of_beq_eq_true h)
  have hhi' : lo + jn J a = 4096 ∨ k < kD TT (jpi J (lo + jn J a)) := by
    cases h : Nat.beq (lo + jn J a) 4096
    · change Bool.rec _ _ (Nat.beq (lo + jn J a) 4096) = true at hhi
      rw [h] at hhi
      change Nat.blt _ _ = true at hhi
      rw [Nat.blt_eq] at hhi
      exact Or.inr hhi
    · exact Or.inl (Nat.eq_of_beq_eq_true h)
  have heq' : ∀ j < jn J a, kD TT (jpi J (lo + j)) = k := fun j hj => Nat.eq_of_beq_eq_true (heq j hj)
  rw [← Finset.sum_filter]
  have hf : (Finset.range 4096).filter (fun j => k = kD TT (jpi J j)) =
      Finset.Ico lo (lo + jn J a) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    constructor
    · rintro ⟨hj, e⟩
      refine ⟨?_, ?_⟩
      · by_contra hc
        rcases hlo' with h | h
        · omega
        · have := hmono j (lo - 1) (by omega) (by omega)
          omega
      · by_contra hc
        rcases hhi' with h | h
        · omega
        · have := hmono (lo + jn J a) j (by omega) hj
          omega
    · rintro ⟨h1, h2⟩
      refine ⟨by omega, ?_⟩
      have := heq' (j - lo) (by omega)
      rw [show lo + (j - lo) = j by omega] at this
      exact this.symm
  rw [hf, Finset.sum_Ico_eq_sum_range, show lo + jn J a - lo = jn J a by omega]
  exact Finset.sum_congr rfl fun _ _ => rfl

theorem keys_sum_eq {TT : ℕ → ℕ} {w : Model.Pauli} {J : ℕ → ℕ} (hs : sortOK TT J = true)
    (hb : ∀ a < 4096, blockOK TT w J a = true) {v : ℕ → ℕ} (hv : ∀ k < 8, partOK TT w J k (v k) = true) :
    ∑ a ∈ Finset.range 4096, ∑ d ∈ Finset.range 4096,
      (if kA TT w a = kD TT d then hW TT w a d else 0) = ∑ k ∈ Finset.range 8, v k := by
  rw [Finset.sum_congr rfl fun a ha => block_sum hs (hb a (Finset.mem_range.1 ha)),
    show (4096 : ℕ) = 512 * 8 from rfl, sum_blocks]
  refine Finset.sum_congr rfl fun k hk => ?_
  have := hv k (Finset.mem_range.1 hk)
  rw [partOK, Nat.beq_eq, sumN_eq] at this
  rw [← this]
  rfl

theorem testBit24 {s a d : ℕ} (hs : s < 2) (ha : a < 4096) (hd : d < 4096) :
    (2 ^ 24 * s + (4096 * d + a)).testBit 24 = decide (s = 1) := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  congr 1
  apply propext
  omega

theorem countSq_eq_keys {TT : ℕ → ℕ} {tA tB : Array Model.Pauli} (hT : TabSpec TT tA tB)
    (w : Model.Pauli) : Rep4371.Native.CosetEnum.countSq tA tB w =
      ∑ a ∈ Finset.range 4096, ∑ d ∈ Finset.range 4096,
        (if kA TT w a = kD TT d then hW TT w a d else 0) := by
  rw [countSq_eq, Finset.card_filter, show (2 : ℕ) ^ 25 = 2 ^ 24 * 2 from rfl, sum_blocks]
  have inner : ∀ k, ∑ i ∈ Finset.range (2 ^ 24),
      (if Rep4371.Native.CosetEnum.sqTest tA tB w (2 ^ 24 * k + i) = true then 1 else 0) =
      ∑ d ∈ Finset.range 4096, ∑ a ∈ Finset.range 4096,
        (if Rep4371.Native.CosetEnum.sqTest tA tB w (2 ^ 24 * k + (4096 * d + a)) = true
          then 1 else 0) := fun k => by
    rw [show Finset.range (2 ^ 24) = Finset.range (4096 * 4096) from rfl, sum_blocks]
  rw [Finset.sum_congr rfl fun k _ => inner k, Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a ha => ?_
  have ha' := Finset.mem_range.1 ha
  have hd' := Finset.mem_range.1 hd
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, Nat.zero_add,
    sqTest_eq_sqW hT, sqTest_eq_sqW hT]
  have e : ∀ s < 2, sqW TT w (2 ^ 24 * s + (4096 * d + a)) =
      andB (Nat.beq (kA TT w a) (kD TT d)) (oneW (prodW TT w (decide (s = 1)) a d)) := by
    intro s hs
    unfold sqW
    obtain ⟨d1, d2, d3⟩ := dec_parts (2 ^ 24 * s + (4096 * d + a))
    rw [d1, d2, d3, testBit24 hs ha' hd', show (2 ^ 24 * s + (4096 * d + a)) % 2 ^ 12 = a by omega,
      show (2 ^ 24 * s + (4096 * d + a)) / 2 ^ 12 % 2 ^ 12 = d by omega]
  rw [e 0 (by norm_num), e 1 (by norm_num)]
  unfold hW
  by_cases hk : kA TT w a = kD TT d
  · rw [if_pos hk, hk, Nat.beq_refl]
    simp only [decide_eq_true_eq]
    cases oneW (prodW TT w false a d) <;> cases oneW (prodW TT w true a d) <;> rfl
  · have hf : Nat.beq (kA TT w a) (kD TT d) = false := by
      cases h : Nat.beq (kA TT w a) (kD TT d)
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true h) hk
    rw [if_neg hk, hf]
    rfl

end CertificateChecks.Coset3023

end
