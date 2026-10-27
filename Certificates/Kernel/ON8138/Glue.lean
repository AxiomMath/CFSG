
module

public import CFSG.Certificates.Kernel.ON8138.Sound
public import Certificates.Kernel.ON8138.Checks
public import Certificates.Kernel.ON8138.Leaves0
public import Certificates.Kernel.ON8138.Leaves1
public import Certificates.Kernel.ON8138.Leaves2

public section

namespace CertificateChecks.KernelON8138

open CFSG.KC.ON8138 CFSG.KD.ON8138 CFSG.RankThree.Native.ONTriple Matrix

theorem codes_len : R0codes.length = 320 := by decide +kernel

theorem words_len : R0words.length = 320 := by decide +kernel

theorem codes_valid : ∀ l ∈ R0codes, l.length = 16 ∧ ∀ x ∈ l, x < 3 := by decide +kernel

theorem words_lt : ∀ w ∈ R0words, ∀ k ∈ w, k < 2 := by decide +kernel

theorem listOK_sound {R : ℕ → ℕ} : ∀ (L : List (List ℕ)) (i : ℕ), listOK R L i = true →
    ∀ k (hk : k < L.length), R (i + k) = packL L[k]
  | [], _, _, k, hk => absurd hk (Nat.not_lt_zero k)
  | l :: L, i, h, k, hk => by
    have e : listOK R (l :: L) i = andK (Nat.beq (R i) (packL l)) (listOK R L (i + 1)) := rfl
    rw [e, andK_eq, Bool.and_eq_true, Nat.beq_eq] at h
    cases k with
    | zero => exact h.1
    | succ k =>
      rw [show i + (k + 1) = (i + 1) + k by omega]
      exact listOK_sound L (i + 1) h.2 k (by simpa using hk)

theorem r0_parts : listOK R0K R0codes 0 = true ∧ memK R0K IK = true ∧
    ∀ i < 320, memK R0K (mulK (R0K i) M0K) = true ∧ memK R0K (mulK (R0K i) M1K) = true ∧
      R0I i < 320 ∧ mulK (R0K (R0I i)) (R0K i) = IK := by
  have h := r0
  unfold r0OK at h
  simp only [andK_eq, Bool.and_eq_true, allK_iff, Nat.blt_eq, Nat.beq_eq] at h
  exact h

theorem R0K_eq (i : ℕ) (hi : i < R0codes.length) : R0K i = packL R0codes[i] := by
  have := listOK_sound R0codes 0 r0_parts.1 i hi
  rwa [Nat.zero_add] at this

theorem decK_R0K (i : ℕ) (hi : i < R0codes.length) : decK (R0K i) = toM4 R0codes[i] := by
  have hv := codes_valid _ (List.getElem_mem hi)
  rw [R0K_eq i hi, decK_packL hv.1 hv.2]

theorem R0K_lt (i : ℕ) (hi : i < R0codes.length) : R0K i < 3 ^ 16 := by
  have hv := codes_valid _ (List.getElem_mem hi)
  rw [R0K_eq i hi]
  exact packL_lt hv.1 hv.2

theorem mem_iff {s : M4} : s ∈ R0list ↔ ∃ i < 320, decK (R0K i) = s := by
  rw [R0list, List.mem_map]
  constructor
  · rintro ⟨l, hl, rfl⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hl
    exact ⟨i, by rwa [codes_len] at hi, decK_R0K i hi⟩
  · rintro ⟨i, hi, rfl⟩
    have hi' : i < R0codes.length := by rwa [codes_len]
    exact ⟨_, List.getElem_mem hi', (decK_R0K i hi').symm⟩

theorem R0K_mem {i : ℕ} (hi : i < 320) : decK (R0K i) ∈ R0list := mem_iff.2 ⟨i, hi, rfl⟩

theorem memK_iff {c : ℕ} (hc : c < 3 ^ 16) : memK R0K c = true ↔ decK c ∈ R0list := by
  rw [memK, anyK_iff, mem_iff]
  constructor
  · rintro ⟨k, hk, h⟩
    exact ⟨k, hk, by rw [Nat.eq_of_beq_eq_true h]⟩
  · rintro ⟨k, hk, h⟩
    refine ⟨k, hk, ?_⟩
    rw [decK_inj h (R0K_lt k (by rwa [codes_len])) hc]
    exact Nat.beq_refl c

theorem one_mem : (1 : M4) ∈ R0list := by
  rw [← decK_IK, ← memK_iff IK_lt]
  exact r0_parts.2.1

theorem mul_matNM_mem {s : M4} (hs : s ∈ R0list) (k : ℕ) : s * matNM k ∈ R0list := by
  obtain ⟨i, hi, rfl⟩ := mem_iff.1 hs
  obtain ⟨h0, h1, -⟩ := r0_parts.2.2 i hi
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [← decK_M0K, ← decK_mulK, ← memK_iff (mulK_lt _ _)]
    exact h0
  · rw [matNM_of_ne (by omega), ← decK_M1K, ← decK_mulK, ← memK_iff (mulK_lt _ _)]
    exact h1

theorem inv_mem {s : M4} (hs : s ∈ R0list) : ∃ s' ∈ R0list, s' * s = 1 := by
  obtain ⟨i, hi, rfl⟩ := mem_iff.1 hs
  obtain ⟨-, -, hI, he⟩ := r0_parts.2.2 i hi
  exact ⟨_, R0K_mem hI, by rw [← decK_mulK, he, decK_IK]⟩

theorem wordsOK_sound : ∀ (W L : List (List ℕ)), wordsOK W L = true →
    ∀ k (h1 : k < W.length) (h2 : k < L.length), foldK W[k] IK = packL L[k]
  | [], _, _, k, h1, _ => absurd h1 (Nat.not_lt_zero k)
  | _ :: _, [], _, k, _, h2 => absurd h2 (Nat.not_lt_zero k)
  | w :: W, l :: L, h, k, h1, h2 => by
    have e : wordsOK (w :: W) (l :: L) = andK (Nat.beq (foldK w IK) (packL l)) (wordsOK W L) := rfl
    rw [e, andK_eq, Bool.and_eq_true, Nat.beq_eq] at h
    cases k with
    | zero => exact h.1
    | succ k => exact wordsOK_sound W L h.2 k (by simpa using h1) (by simpa using h2)

theorem words_eq (i : ℕ) (h1 : i < R0words.length) (h2 : i < R0codes.length) :
    ((R0words[i]'h1).map fun k => matNM k).prod = toM4 (R0codes[i]'h2) := by
  have hv := codes_valid _ (List.getElem_mem h2)
  have e : foldK (R0words[i]'h1) IK = packL (R0codes[i]'h2) := wordsOK_sound R0words R0codes words i h1 h2
  have := congrArg decK e
  rwa [decK_foldK, decK_IK, one_mul, decK_packL hv.1 hv.2] at this

theorem word_of_mem {s : M4} (hs : s ∈ R0list) : ∃ w : List ℕ, s = (w.map fun k => matNM k).prod := by
  rw [R0list, List.mem_map] at hs
  obtain ⟨l, hl, rfl⟩ := hs
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hl
  have h1 : i < R0words.length := by rw [words_len]; rwa [codes_len] at hi
  exact ⟨_, (words_eq i h1 hi).symm⟩

theorem mul_word_mem {s : M4} (hs : s ∈ R0list) (w : List ℕ) :
    s * (w.map fun k => matNM k).prod ∈ R0list := by
  induction w generalizing s with
  | nil => rwa [List.map_nil, List.prod_nil, mul_one]
  | cons k w ih =>
    rw [List.map_cons, List.prod_cons, ← mul_assoc]
    exact ih (mul_matNM_mem hs k)

theorem mul_mem {s s' : M4} (hs : s ∈ R0list) (hs' : s' ∈ R0list) : s * s' ∈ R0list := by
  obtain ⟨w, rfl⟩ := word_of_mem hs'
  exact mul_word_mem hs w

theorem conj_mem {U T : M4} (hTU : T * U = 1) (hA : U * matNM 0 * T ∈ R0list)
    (hB : U * matNM 1 * T ∈ R0list) {X : M4} (hX : X ∈ R0list) : U * X * T ∈ R0list := by
  obtain ⟨w, rfl⟩ := word_of_mem hX
  clear hX
  induction w with
  | nil =>
    rw [List.map_nil, List.prod_nil, mul_one, mul_eq_one_comm.1 hTU]
    exact one_mem
  | cons k w ih =>
    have hk : U * matNM k * T ∈ R0list := by
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · exact hA
      · rwa [matNM_of_ne (by omega)]
    rw [List.map_cons, List.prod_cons,
      show U * (matNM k * (w.map fun k => matNM k).prod) * T =
        (U * matNM k * T) * (U * (w.map fun k => matNM k).prod * T) by
        rw [show U * matNM k * T * (U * (w.map fun k => matNM k).prod * T) =
          U * matNM k * (T * U) * (w.map fun k => matNM k).prod * T by
          simp only [Matrix.mul_assoc], hTU, Matrix.mul_one]
        simp only [Matrix.mul_assoc]]
    exact mul_mem hk ih

theorem TK_zero : decK (TK 0) = 1 := by
  have h := cos
  unfold cosOK at h
  rw [andK_eq, Bool.and_eq_true, Nat.beq_eq] at h
  rw [h.1, decK_IK]

theorem coset_facts {j : ℕ} (hj0 : 0 < j) (hj : j < 162) :
    (∃ ti : M4, ti * decK (TK j) = 1 ∧
      ¬ (ti * matNM 0 * decK (TK j) ∈ R0list ∧ ti * matNM 1 * decK (TK j) ∈ R0list)) ∧
    (∃ r ∈ R0list, ∃ k < 10, (r * decK (TK j)) ^ k ≠ 1 ∧ ((r * decK (TK j)) ^ k) ^ 3 = 1) := by
  have h := cos
  unfold cosOK at h
  rw [andK_eq, Bool.and_eq_true, allK_iff] at h
  have hc := h.2 (j - 1) (by change j - 1 < 161; omega)
  rw [show Nat.succ (j - 1) = j by omega] at hc
  unfold cosJ at hc
  simp only [andK_eq, notK_eq, strictN_eq, Bool.and_eq_true, Bool.not_eq_true', Nat.beq_eq,
    Nat.blt_eq] at hc
  obtain ⟨hti, hn, hr, hk, hB, hB3⟩ := hc
  refine ⟨⟨decK (TI j), by rw [← decK_mulK, hti, decK_IK], fun ⟨hA, hB'⟩ => ?_⟩,
    ⟨decK (R0K _), R0K_mem hr, _, hk, fun he => ?_, ?_⟩⟩
  · rw [← decK_M0K, ← decK_mulK, ← decK_mulK, ← memK_iff (mulK_lt _ _)] at hA
    rw [← decK_M1K, ← decK_mulK, ← decK_mulK, ← memK_iff (mulK_lt _ _)] at hB'
    rw [hA, hB'] at hn
    exact absurd hn (by decide)
  · have e := decK_inj (by rw [decK_powK, decK_mulK, he, decK_IK]) (powK_lt _ _) IK_lt
    rw [e, Nat.beq_refl] at hB
    exact absurd hB (by decide)
  · rw [← decK_mulK, ← decK_powK, ← decK_powK, hB3, decK_IK]

theorem leaf_facts {T s : M4} {j : ℕ} (hj : j < 162) (hs : s ∈ R0list)
    (hT : T = s * decK (TK j)) (h1 : T * symInvM T = 1) :
    (symInvM T * matNM 0 * T ∈ R0list → symInvM T * matNM 1 * T ∈ R0list → T ∈ R0list) ∧
      (T ∈ R0list ∨ ∃ r ∈ R0list, ∃ k < 10, (r * T) ^ k ≠ 1 ∧ ((r * T) ^ k) ^ 3 = 1) := by
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · rw [TK_zero, mul_one] at hT
    subst hT
    exact ⟨fun _ _ => hs, Or.inl hs⟩
  obtain ⟨⟨ti, hti, hn⟩, ⟨r, hr, k, hk, hne, h3⟩⟩ := coset_facts hj0 hj
  obtain ⟨s', hs', hss'⟩ := inv_mem hs
  have hss : s * s' = 1 := mul_eq_one_comm.1 hss'
  set t := decK (TK j)
  set U := symInvM T
  have hUT : U * T = 1 := mul_eq_one_comm.1 h1
  have ht : s' * T = t := by rw [hT, ← Matrix.mul_assoc, hss', Matrix.one_mul]
  refine ⟨fun hA hB => ?_, Or.inr ⟨r * s', mul_mem hr hs', k, hk, ?_⟩⟩
  · exfalso
    have hUs : U * s * t = 1 := by rw [Matrix.mul_assoc, ← hT, hUT]
    have hti' : ti = U * s := by
      have h2 : t * (U * s) = 1 := mul_eq_one_comm.1 hUs
      rw [← Matrix.mul_one ti, ← h2, ← Matrix.mul_assoc, hti, Matrix.one_mul]
    apply hn
    have key : ∀ m : ℕ, ti * matNM m * t = U * (s * matNM m * s') * T := by
      intro m
      rw [hti', ← ht]
      simp only [Matrix.mul_assoc]
    rw [key 0, key 1]
    exact ⟨conj_mem h1 hA hB (mul_mem (mul_matNM_mem hs 0) hs'),
      conj_mem h1 hA hB (mul_mem (mul_matNM_mem hs 1) hs')⟩
  · have e : r * s' * T = r * t := by rw [Matrix.mul_assoc, ht]
    rw [e]
    exact ⟨hne, h3⟩

theorem memA_iff' {a : Array ℕ} (ha : ValidA a) : memA a = true ↔ decA a ∈ R0list := by
  rw [memA, List.contains_iff_mem, R0arrs, List.mem_map, R0list, List.mem_map]
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact ⟨l, hl, (decA_toArray l).symm⟩
  · rintro ⟨l, hl, hle⟩
    refine ⟨l, hl, ?_⟩
    apply decA_injective (validA_toArray (codes_valid l hl).1 (codes_valid l hl).2) ha
    rw [decA_toArray, hle]

theorem spLeafA_of {T : M4} (h1 : T * symInvM T = 1)
    (h2 : symInvM T * matNM 0 * T ∈ R0list → symInvM T * matNM 1 * T ∈ R0list → T ∈ R0list)
    (h3 : T ∈ R0list ∨ ∃ r ∈ R0list, ∃ k < 10, (r * T) ^ k ≠ 1 ∧ ((r * T) ^ k) ^ 3 = 1) :
    spLeafA (encA T) = true := by
  have hT := validA_encA T
  have hU1 : amul (encA T) (symInvA (encA T)) = idA := by
    apply decA_injective (validA_amul _ _) validA_idA
    rw [decA_amul, decA_encA, decA_symInvA, h1, decA_idA]
  have hm0 : memA (amul (amul (symInvA (encA T)) M0A) (encA T)) = true ↔
      symInvM T * matNM 0 * T ∈ R0list := by
    rw [memA_iff' (validA_amul _ _), decA_amul, decA_amul, decA_symInvA, decA_M0A, decA_encA]
  have hm1 : memA (amul (amul (symInvA (encA T)) M1A) (encA T)) = true ↔
      symInvM T * matNM 1 * T ∈ R0list := by
    rw [memA_iff' (validA_amul _ _), decA_amul, decA_amul, decA_symInvA, decA_M1A, decA_encA]
  have hmT : memA (encA T) = true ↔ T ∈ R0list := by rw [memA_iff' hT, decA_encA]
  unfold spLeafA
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq, List.any_eq_true,
    List.mem_range, bne_iff_ne, ne_eq]
  refine ⟨⟨hU1, ?_⟩, ?_⟩
  · by_cases hA : symInvM T * matNM 0 * T ∈ R0list
    · by_cases hB : symInvM T * matNM 1 * T ∈ R0list
      · exact Or.inr (hmT.2 (h2 hA hB))
      · exact Or.inl (Or.inr (by rw [← Bool.not_eq_true, hm1]; exact hB))
    · exact Or.inl (Or.inl (by rw [← Bool.not_eq_true, hm0]; exact hA))
  · rcases h3 with h3 | ⟨r, hr, k, hk, hne, hcube⟩
    · exact Or.inl (hmT.2 h3)
    · right
      rw [R0list, List.mem_map] at hr
      obtain ⟨l, hl, rfl⟩ := hr
      refine ⟨l.toArray, List.mem_map_of_mem hl, k, hk, fun he => hne ?_, ?_⟩
      · have := congrArg decA he
        rwa [decA_apow, decA_amul, decA_toArray, decA_encA, decA_idA] at this
      · apply decA_injective (validA_apow _ _) validA_idA
        rw [decA_apow, decA_apow, decA_amul, decA_toArray, decA_encA, decA_idA]
        exact hcube

theorem leafK_sound {a b c d : ℕ} (h : leafK R0K TK WK a b c d = true) :
    ∃ i < 320, ∃ j < 162, mulK (R0K i) (TK j) = codeK a b c d := by
  unfold leafK at h
  rw [strictN_eq] at h
  unfold leafW at h
  simp only [andK_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
  exact ⟨_, h.1, _, h.2.1, h.2.2⟩

theorem mask_bit {v x d : ℕ} (hv : v < 3) (hx : x < 81) (hd : d < 81) :
    bitK (MK (81 * v + x)) d = Nat.beq (pairK x d) v := by
  have h := mask
  unfold maskOK at h
  rw [allK_iff] at h
  have h := h v hv
  rw [allK_iff] at h
  have h := h x hx
  rw [allK_iff] at h
  have h := h d hd
  rw [nadd, nmul] at h
  cases e : Nat.beq (pairK x d) v
  · rw [e, notK_eq, Bool.not_eq_true'] at h
    exact h
  · rw [e] at h
    exact h

theorem m0 {x d : ℕ} (hx : x < 81) (hd : d < 81) : bitK (MK x) d = Nat.beq (pairK x d) 0 := by
  have := mask_bit (v := 0) (by norm_num) hx hd
  rwa [Nat.mul_zero, Nat.zero_add] at this

theorem m1 {x d : ℕ} (hx : x < 81) (hd : d < 81) :
    bitK (MK (Nat.add 81 x)) d = Nat.beq (pairK x d) 1 := by
  have := mask_bit (v := 1) (by norm_num) hx hd
  rwa [Nat.mul_one] at this

theorem m2 {x d : ℕ} (hx : x < 81) (hd : d < 81) :
    bitK (MK (Nat.add 162 x)) d = Nat.beq (pairK x d) 2 := by
  have := mask_bit (v := 2) (by norm_num) hx hd
  rwa [show 81 * 2 = 162 from rfl] at this

theorem spA_sound {a b c d : ℕ} (h : spA R0K TK WK MK a = true) (ha : a < 81) (hb : b < 81)
    (hc : c < 81) (hd : d < 81) (hab : pairK a b = 0) (hac : pairK a c = 0) (hbc : pairK b c = 2)
    (had : pairK a d = 1) (hbd : pairK b d = 2) (hcd : pairK c d = 0) :
    leafK R0K TK WK a b c d = true := by
  unfold spA at h
  rw [allK_iff] at h
  have h := h b hb
  rw [orK_eq, notK_eq, m0 ha hb, hab] at h
  simp only [Nat.beq_refl, Bool.not_true, Bool.false_or] at h
  rw [strictN_eq, allK_iff] at h
  have h := h c hc
  rw [orK_eq, notK_eq, bitK_land, m0 ha hc, m2 hb hc, hac, hbc] at h
  simp only [Nat.beq_refl, Bool.and_self, Bool.not_true, Bool.false_or] at h
  rw [strictN_eq, allK_iff] at h
  have h := h d hd
  rw [orK_eq, notK_eq, bitK_land, bitK_land, m1 ha hd, m2 hb hd, m0 hc hd, had, hbd, hcd] at h
  simpa only [Nat.beq_refl, Bool.and_self, Bool.not_true, Bool.false_or] using h

theorem spA_all {a : ℕ} (ha : a < 81) : spA R0K TK WK MK a = true := by
  have H : ∀ lo, spRange R0K TK WK MK lo 9 = true → ∀ k < 9, spA R0K TK WK MK (lo + k) = true :=
    fun lo h k hk => (allK_iff _ _).1 h k hk
  have e : a = 9 * (a / 9) + a % 9 := (Nat.div_add_mod a 9).symm
  have hr : a % 9 < 9 := Nat.mod_lt _ (by norm_num)
  have hq : a / 9 < 9 := by omega
  rw [e]
  interval_cases (a / 9)
  · exact H 0 leaves0 _ hr
  · exact H 9 leaves1 _ hr
  · exact H 18 leaves2 _ hr
  · exact H 27 leaves3 _ hr
  · exact H 36 leaves4 _ hr
  · exact H 45 leaves5 _ hr
  · exact H 54 leaves6 _ hr
  · exact H 63 leaves7 _ hr
  · exact H 72 leaves8 _ hr

theorem leaf_ok {a b c d : ℕ} (ha : a < 81) (hb : b < 81) (hc : c < 81) (hd : d < 81)
    (hab : pairK a b = 0) (hac : pairK a c = 0) (hbc : pairK b c = 2) (had : pairK a d = 1)
    (hbd : pairK b d = 2) (hcd : pairK c d = 0) :
    spLeafA (encA (Matrix.of ![vdec a, vdec b, vdec c, vdec d])) = true := by
  obtain ⟨i, hi, j, hj, he⟩ :=
    leafK_sound (spA_sound (spA_all ha) ha hb hc hd hab hac hbc had hbd hcd)
  have hT : (Matrix.of ![vdec a, vdec b, vdec c, vdec d] : M4) = decK (R0K i) * decK (TK j) := by
    rw [← decK_codeK ha hb hc hd, ← he, decK_mulK]
  rw [pairK_eq] at hab hac hbc had hbd hcd
  have h1 := mul_symInvM
    (symp_of_pairs (T := Matrix.of ![vdec a, vdec b, vdec c, vdec d]) hab hac hbc had hbd hcd)
  obtain ⟨h2, h3⟩ := leaf_facts hj (R0K_mem hi) hT h1
  exact spLeafA_of h1 h2 h3

theorem tp_get {x y : ℕ} (hx : x < 81) (hy : y < 81) : tpTab[x * 81 + y]! = pairK x y := by
  rw [tpTab_getElem! hx hy, pairK_eq]

theorem spCheckA_true : spCheckA = true := by
  simp only [spCheckA, List.all_eq_true, List.mem_range, Bool.or_eq_true, bne_iff_ne, ne_eq]
  intro a ha b hb
  rw [tp_get ha hb]
  by_cases hab : pairK a b = 0
  swap
  · exact Or.inl hab
  refine Or.inr fun c hc => ?_
  rw [tp_get ha hc, tp_get hb hc]
  by_cases hac : pairK a c = 0
  swap
  · exact Or.inl (Or.inl hac)
  by_cases hbc : pairK b c = 2
  swap
  · exact Or.inl (Or.inr hbc)
  refine Or.inr fun d hd => ?_
  rw [tp_get ha hd, tp_get hb hd, tp_get hc hd]
  by_cases had : pairK a d = 1
  swap
  · exact Or.inl (Or.inl (Or.inl had))
  by_cases hbd : pairK b d = 2
  swap
  · exact Or.inl (Or.inl (Or.inr hbd))
  by_cases hcd : pairK c d = 0
  swap
  · exact Or.inl (Or.inr hcd)
  exact Or.inr (leaf_ok ha hb hc hd hab hac hbc had hbd hcd)

theorem validA_foldl (w : List ℕ) {a : Array ℕ} (ha : ValidA a) :
    ValidA (w.foldl (fun a k => amul a (if k = 0 then M0A else M1A)) a) := by
  induction w generalizing a with
  | nil => exact ha
  | cons k w ih => exact ih (validA_amul _ _)

theorem r0Check_true : r0Check = true := by
  unfold r0Check
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range, decide_eq_true_eq]
  refine ⟨⟨⟨⟨codes_len, words_len⟩, fun i hi => ?_⟩, codes_valid⟩, words_lt⟩
  have hi1 : i < R0codes.length := by rw [codes_len]; exact hi
  have hi2 : i < R0words.length := by rw [words_len]; exact hi
  rw [List.getD_eq_getElem _ _ hi2, List.getD_eq_getElem _ _ hi1]
  have hv := codes_valid _ (List.getElem_mem hi1)
  apply decA_injective (validA_foldl _ validA_idA) (validA_toArray hv.1 hv.2)
  rw [foldl_amul, decA_idA, one_mul, decA_toArray, words_eq i hi2 hi1]

end CertificateChecks.KernelON8138

end
