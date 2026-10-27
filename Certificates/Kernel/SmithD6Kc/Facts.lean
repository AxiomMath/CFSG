module

public import Certificates.Kernel.SmithD6Kc.Checks
public import Certificates.Kernel.SmithD6Wt.Math
public import Certificates.Kernel.SmithD6Trees.Facts
public import CFSG.Certificates.Kernel.SmithD6KcSound
public import Certificates.Data.SmithD6Kc

set_option maxRecDepth 100000

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CertificateChecks.SmithD6Kc

open CFSG.SmithD6 CFSG.KC.KeyTree CFSG.KD.SmithD6 CFSG.GF2Type.SmithTypeE.DMod

theorem flatten_getD_chunk {α : Type} (d : α) (n : ℕ) : ∀ (cs : List (List α)),
    (∀ c, c + 1 < cs.length → (cs.getD c []).length = n) →
    ∀ c k, c < cs.length → k < (cs.getD c []).length →
      cs.flatten.getD (n * c + k) d = (cs.getD c []).getD k d
  | [], _, _, _, hc, _ => absurd hc (by simp)
  | a :: cs, h, c, k, hc, hk => by
    rw [List.flatten_cons]
    rcases c with _ | c
    · rw [Nat.mul_zero, Nat.zero_add, List.getD_cons_zero] at *
      exact SmithD6Wt.getD_append_left' d hk
    · have ha : a.length = n := by simpa using h 0 (by simp at hc ⊢; omega)
      rw [SmithD6Wt.getD_append_right' d (by rw [ha]; nlinarith), ha,
        show n * (c + 1) + k - n = n * c + k by rw [Nat.mul_succ]; omega, List.getD_cons_succ]
      exact flatten_getD_chunk d n cs (fun c' hc' => by simpa using h (c' + 1) (by simpa using hc'))
        c k (by simpa using hc) (by simpa using hk)

theorem pbC_chunk_length {c : ℕ} (hc : c < 37) :
    (J.pbC.getD c []).length = (if c + 1 < 37 then 2048 else 2007) ∧
      (J.ppC.getD c []).length = (J.pbC.getD c []).length := by
  have hl : J.wt64C.length = 37 := SmithD6Wt.wt64C_length
  have hc' : c < J.wt64C.length := by rw [hl]; exact hc
  obtain ⟨-, hlen, -⟩ := chunkOK_sound hc' (SmithD6Wt.wt64Chunks_ok c hc)
  obtain ⟨h1, h2, -⟩ := SmithD6Wt.planes c hc
  rw [getD_eq hc'] at h1 h2
  refine ⟨?_, by rw [h1, h2]⟩
  rw [h1]
  split_ifs at hlen ⊢ <;> omega

theorem pb_flat_getD {j : ℕ} (hj : j < 75735) :
    J.pbC.flatten.getD j #[] = (J.pbC.getD (j / 2048) []).getD (j % 2048) #[] ∧
      J.ppC.flatten.getD j #[] = (J.ppC.getD (j / 2048) []).getD (j % 2048) #[] ∧
      j % 2048 < (J.pbC.getD (j / 2048) []).length := by
  obtain ⟨hl1, hl2⟩ := SmithD6Wt.pbC_ppC_length
  have hc : j / 2048 < 37 := by omega
  have hk : j % 2048 < (J.pbC.getD (j / 2048) []).length := by
    rw [(pbC_chunk_length hc).1]
    split_ifs with h <;> omega
  have e : 2048 * (j / 2048) + j % 2048 = j := Nat.div_add_mod j 2048
  refine ⟨?_, ?_, hk⟩
  · rw [← flatten_getD_chunk #[] 2048 J.pbC (fun c hc' => by
      rw [(pbC_chunk_length (by omega)).1, if_pos (by omega)]) _ _ (by omega) hk, e]
  · rw [← flatten_getD_chunk #[] 2048 J.ppC (fun c hc' => by
      rw [(pbC_chunk_length (by omega)).2, (pbC_chunk_length (by omega)).1, if_pos (by omega)])
      _ _ (by omega) (by rw [(pbC_chunk_length hc).2]; exact hk), e]

theorem pb_size {j : ℕ} (hj : j < 75735) :
    (J.pbC.flatten.getD j #[]).size = 6 ∧ (J.ppC.flatten.getD j #[]).size = 6 := by
  obtain ⟨e1, e2, hk⟩ := pb_flat_getD hj
  have hc : j / 2048 < 37 := by omega
  obtain ⟨h1, h2, h3⟩ := SmithD6Wt.planes (j / 2048) hc
  have h := h3 (j % 2048) (by rw [← h1]; exact hk)
  obtain ⟨-, l1, l2, -⟩ := planeL_sound h
  rw [e1, e2, ← Array.length_toList, ← Array.length_toList]
  exact ⟨l1, l2⟩

theorem memR_eq_kcMem' {B P : Array ℕ} (hB : B.size = 6) (hP : P.size = 6) (x : ℕ) :
    memR B P x = kcMem B.toList P.toList x := by
  rcases B with ⟨bs⟩
  rcases P with ⟨ps⟩
  exact memR_eq_kcMem hB hP x

theorem length_filter_eq_sum (p : ℕ → Bool) : ∀ l : List ℕ,
    (l.filter p).length = (l.map fun i => if p i then 1 else 0).sum
  | [] => rfl
  | a :: l => by
    rw [List.filter_cons, List.map_cons, List.sum_cons, ← length_filter_eq_sum p l]
    cases p a <;> simp <;> omega

theorem zipWith_eq_map_range {f : Array ℕ → Array ℕ → ℕ} {L1 L2 : List (Array ℕ)} {N : ℕ}
    (h1 : L1.length = N) (h2 : L2.length = N) :
    List.zipWith f L1 L2 = (List.range N).map fun i => f (L1.getD i #[]) (L2.getD i #[]) := by
  apply List.ext_getElem (by simp [h1, h2])
  intro i hi hi'
  simp only [List.getElem_zipWith, List.getElem_map, List.getElem_range]
  rw [getD_eq (by simp at hi'; omega), getD_eq (by simp at hi'; omega)]

theorem chkKcThrough_of_pinned (hpb : ∀ i < 75735, pbArr[i]! = J.pbC.flatten.getD i #[])
    (hpp : ∀ i < 75735, ppArr[i]! = J.ppC.flatten.getD i #[]) : chkKcThrough = true := by
  have hl := SmithD6Wt.pbC_ppC_length
  have hlpb : J.pbC.flatten.length = 75735 := SmithD6Wt.planes_flat.1
  have hlpp : J.ppC.flatten.length = 75735 := by
    rw [← hlpb, List.length_flatten, List.length_flatten]
    refine congrArg List.sum (List.ext_getElem (by simp [hl.1, hl.2]) fun c h1 h2 => ?_)
    have hc : c < 37 := by simpa [hl.2] using h1
    simp only [List.getElem_map]
    have := (pbC_chunk_length hc).2
    rw [getD_eq (by omega), getD_eq (by omega)] at this
    exact this
  have hsum := thrAll_ok
  rw [kcThrAll, kcThrC_eq J.pbC J.ppC (by rw [hl.1, hl.2]) fun c hc =>
    ((pbC_chunk_length (by rw [hl.1] at hc; exact hc)).2).symm,
    zipWith_eq_map_range hlpb hlpp] at hsum
  unfold chkKcThrough
  rw [beq_iff_eq, length_filter_eq_sum, ← hsum]
  refine congrArg List.sum (List.map_congr_left ?_)
  intro i hi
  have hi' := List.mem_range.1 hi
  obtain ⟨s1, s2⟩ := pb_size hi'
  rw [hpb i hi', hpp i hi', memR_eq_kcMem' s1 s2, memR_eq_kcMem' s1 s2]
  rcases hB : J.pbC.flatten.getD i #[] with ⟨bs⟩
  rcases hP : J.ppC.flatten.getD i #[] with ⟨ps⟩
  change _ = nIf(kcMem bs ps 64, nIf(kcMem bs ps 128, 1, 0), 0)
  cases kcMem bs ps 64 <;> cases kcMem bs ps 128 <;> rfl

theorem and63_xor (a b : ℕ) : (a ^^^ b) &&& 63 = (a &&& 63) ^^^ (b &&& 63) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_and, Nat.testBit_xor]
  cases a.testBit i <;> cases b.testBit i <;> simp

theorem card_filter_range_eq (p : ℕ → Bool) (n : ℕ) :
    ((Finset.range n).filter fun d => p d = true).card = ((List.range n).filter p).length := by
  rw [Finset.card_def, Finset.filter_val, Finset.range_val, Multiset.range, Multiset.filter_coe,
    Multiset.coe_card]
  congr 1

theorem four_distinct {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    ∀ t t' : Fin 4, (![0, a, b, a ^^^ b] : Fin 4 → ℕ) t = ![0, a, b, a ^^^ b] t' → t = t' := by
  have x1 : a ^^^ b ≠ 0 := fun e => by
    apply hab
    have := congrArg (· ^^^ b) e
    simpa [Nat.xor_assoc] using this
  have x2 : a ^^^ b ≠ a := fun e => by
    apply hb
    have := congrArg (a ^^^ ·) e
    simpa [← Nat.xor_assoc] using this
  have x3 : a ^^^ b ≠ b := fun e => by
    apply ha
    have := congrArg (· ^^^ b) e
    simpa [Nat.xor_assoc] using this
  intro t t'
  fin_cases t <;> fin_cases t' <;> simp <;> omega

theorem card_le_sixteen {B : Array ℕ} {k l : ℕ} (hk : k < 6) (hl : l < 6)
    (h1 : B[k]! &&& 63 ≠ 0) (h2 : B[l]! &&& 63 ≠ 0) (h3 : B[k]! &&& 63 ≠ B[l]! &&& 63) :
    ((Finset.range 64).filter fun c => xorComb B c &&& 63 = 0).card ≤ 16 := by
  set K := (Finset.range 64).filter fun c => xorComb B c &&& 63 = 0 with hK
  let v : Fin 4 → ℕ := ![0, 2 ^ k, 2 ^ l, 2 ^ k ^^^ 2 ^ l]
  have hv : ∀ t, v t < 64 := by
    have a1 : 2 ^ k < 2 ^ 6 := Nat.pow_lt_pow_right (by norm_num) hk
    have a2 : 2 ^ l < 2 ^ 6 := Nat.pow_lt_pow_right (by norm_num) hl
    intro t
    fin_cases t
    · simp [v]
    · simpa [v] using a1
    · simpa [v] using a2
    · simpa [v] using Nat.xor_lt_two_pow a1 a2
  have he : ∀ t, xorComb B (v t) &&& 63 = (![0, B[k]! &&& 63, B[l]! &&& 63,
      (B[k]! &&& 63) ^^^ (B[l]! &&& 63)] : Fin 4 → ℕ) t := by
    intro t
    fin_cases t
    · simp [v, xorComb_zero]
    · simp [v, xorComb_two_pow B hk]
    · simp [v, xorComb_two_pow B hl]
    · simp [v, xorComb_xor, xorComb_two_pow B hk, xorComb_two_pow B hl, and63_xor]
  have hinj : ∀ t t', xorComb B (v t) &&& 63 = xorComb B (v t') &&& 63 → t = t' := by
    intro t t' e
    rw [he, he] at e
    exact four_distinct h1 h2 h3 t t' e
  have hmap : ∀ p ∈ (Finset.univ : Finset (Fin 4)) ×ˢ K, p.2 ^^^ v p.1 ∈ Finset.range 64 := by
    intro p hp
    have hc : p.2 < 64 := Finset.mem_range.1 (Finset.mem_filter.1 (Finset.mem_product.1 hp).2).1
    exact Finset.mem_range.2 (Nat.xor_lt_two_pow (n := 6) hc (hv p.1))
  have hio : Set.InjOn (fun p : Fin 4 × ℕ => p.2 ^^^ v p.1)
      ↑((Finset.univ : Finset (Fin 4)) ×ˢ K) := by
    rintro ⟨t, c⟩ hp ⟨t', c'⟩ hp' e
    have hc := (Finset.mem_filter.1 (Finset.mem_product.1 hp).2).2
    have hc' := (Finset.mem_filter.1 (Finset.mem_product.1 hp').2).2
    simp only at e hc hc'
    have e2 := congrArg (fun z => xorComb B z &&& 63) e
    simp only [xorComb_xor, and63_xor, hc, hc', Nat.zero_xor] at e2
    have ht := hinj t t' e2
    subst ht
    simp only [Prod.mk.injEq, true_and]
    have := congrArg (fun z => z ^^^ v t) e
    simpa [Nat.xor_assoc] using this
  have hcard := Finset.card_le_card_of_injOn _ hmap hio
  rw [Finset.card_product, Finset.card_univ, Fintype.card_fin, Finset.card_range] at hcard
  omega

theorem meet_le {j : ℕ} (hj : j < 75735) (hj0 : j ≠ 0) :
    ((List.range 64).filter fun d => memR (J.pbC.flatten.getD j #[]) (J.ppC.flatten.getD j #[])
      (xorComb (J.pbC.flatten.getD 0 #[]) d)).length ≤ 16 := by
  set B := J.pbC.flatten.getD j #[] with hB
  set P := J.ppC.flatten.getD j #[] with hP
  obtain ⟨e1, -, hk⟩ := pb_flat_getD hj
  have hc : j / 2048 < 37 := by omega
  have hr : kcRk2A B = true := by
    have h := meetChunks_ok (j / 2048) hc
    rw [d6KcMeetOK, nthA_eq] at h
    rw [hB, e1]
    refine kcMeetGo_sound _ _ h _ hk ?_
    by_cases h0 : j / 2048 = 0
    · right
      omega
    · left
      cases hb : Nat.beq (j / 2048) 0
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true hb) h0
  obtain ⟨x, hx, y, hy, hx0, hy0, hxy⟩ := kcRk2A_sound hr
  have hsz : B.toList.length = 6 := by rw [Array.length_toList]; exact (pb_size hj).1
  obtain ⟨k, hk6, rfl⟩ := List.getElem_of_mem hx
  obtain ⟨l, hl6, rfl⟩ := List.getElem_of_mem hy
  have ek : B[k]! = B.toList[k] := by
    rw [getElem!_eq_getD_toList, getD_eq hk6]
  have el : B[l]! = B.toList[l] := by
    rw [getElem!_eq_getD_toList, getD_eq hl6]
  have h16 := card_le_sixteen (B := B) (k := k) (l := l) (by omega) (by omega) (by rw [ek]; exact hx0)
    (by rw [el]; exact hy0) (by rw [ek, el]; exact hxy)
  rw [← card_filter_range_eq]
  refine le_trans (Finset.card_le_card_of_injOn (fun d => coefOf P (64 * d)) ?_ ?_) h16
  · intro d hd
    obtain ⟨hd64, hm⟩ := Finset.mem_filter.1 hd
    have hd64' := Finset.mem_range.1 hd64
    rw [SmithD6Wt.first.2, xorComb_fBasis_eq d hd64'] at hm
    have hm' : xorComb B (coefOf P (64 * d)) = 64 * d := beq_iff_eq.1 hm
    refine Finset.mem_filter.2 ⟨Finset.mem_range.2 (coefOf_lt P _), ?_⟩
    rw [hm']
    apply Nat.eq_of_testBit_eq
    intro i
    rw [testBit_and_63, Nat.zero_testBit]
    by_cases hi : i < 6
    · rw [decide_eq_true hi, Bool.true_and, testBit_mul_64_of_lt d i hi]
    · rw [decide_eq_false hi, Bool.false_and]
  · intro d hd d' hd' e
    have m1 := (Finset.mem_filter.1 hd).2
    have m2 := (Finset.mem_filter.1 hd').2
    have b1 := Finset.mem_range.1 (Finset.mem_filter.1 hd).1
    have b2 := Finset.mem_range.1 (Finset.mem_filter.1 hd').1
    rw [SmithD6Wt.first.2, xorComb_fBasis_eq _ b1] at m1
    rw [SmithD6Wt.first.2, xorComb_fBasis_eq _ b2] at m2
    have q1 : xorComb B (coefOf P (64 * d)) = 64 * d := beq_iff_eq.1 m1
    have q2 : xorComb B (coefOf P (64 * d')) = 64 * d' := beq_iff_eq.1 m2
    have e' : coefOf P (64 * d) = coefOf P (64 * d') := e
    rw [e'] at q1
    omega

theorem chkKcMeet_of_pinned (hpb : ∀ i < 75735, pbArr[i]! = J.pbC.flatten.getD i #[])
    (hpp : ∀ i < 75735, ppArr[i]! = J.ppC.flatten.getD i #[]) : chkKcMeet = true := by
  unfold chkKcMeet
  rw [List.all_eq_true]
  intro j hj
  have hj' := List.mem_range.1 hj
  by_cases h0 : j = 0
  · simp [h0]
  · have h : meetCnt 0 j ≤ 16 := by
      unfold meetCnt
      rw [hpb 0 (by norm_num), hpb j hj', hpp j hj']
      exact meet_le hj' h0
    simp [h0, h]

theorem chkSpanW_of_pinned (hwt : ∀ j (hj : j < J.wtC.flatten.length), wt j = J.wtC.flatten[j]) :
    chkSpanW = true := by
  have hs := kcSpanGo_sound spanIdx.toList 0 span_ok
  have hlen : spanIdx.toList.length = 32 := by decide
  have em : spanIdx.map (fun i => wtArr[i]!) = ((List.range 32).map (2 ^ ·)).toArray := by
    apply Array.ext'
    rw [Array.toList_map, List.toList_toArray]
    apply List.ext_getElem (by simp [hlen])
    intro m h1 h2
    have hm : m < 32 := by simpa using h2
    have hf := hs m (by omega)
    rw [Nat.zero_add, getD_eq (by omega)] at hf
    obtain ⟨hv, hx⟩ := SmithD6Trees.wt_facts.2.2.2 _ _ hf
    simp only [List.getElem_map, List.getElem_range]
    have e := hwt _ hv
    unfold wt at e
    rw [e, hx]
  unfold chkSpanW
  rw [em, ← Array.all_toList]
  decide +kernel

end CertificateChecks.SmithD6Kc

end
