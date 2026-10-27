module

public import Certificates.Kernel.Syl3W.Check
public import CFSG.Certificates.Kernel.Syl3WSound

public section

open CFSG.KC.Syl3W CFSG.KC.Syl3W.Sound
open CFSG.KC.BalanceSC (getL notB)
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1310u

namespace CFSG.KD.Syl3W

theorem nb (a b : ℕ) : Nat.beq a b = decide (a = b) := by
  cases h : Nat.beq a b
  · exact (decide_eq_false (Nat.ne_of_beq_eq_false h)).symm
  · exact (decide_eq_true (Nat.eq_of_beq_eq_true h)).symm

theorem tabulate_getD {α : Type} {n : ℕ} (f : Fin n → α) (i : Fin n) (d : α) :
    (syl3Tabulate f).getD i.val d = f i := by
  simp [syl3Tabulate, Array.getD_eq_getD_getElem?]

theorem arrOfChars_eq {s : String} {L : List Char} {P len : ℕ} (hs : s = String.ofList L)
    (hc : codesK (L.map Char.toNat) P len = true) {i : ℕ} (hi : 36 * i + 36 ≤ len) :
    syl3ArrOfChars s.toList.toArray i = decM (slot P i) := by
  obtain ⟨hlen, hget⟩ := codesW_spec _ 0 hc
  rw [List.length_map] at hlen
  apply arr_eq_of_getD (by simp [syl3ArrOfChars]) (size_decM _)
  intro e he
  have hm : 36 * i + e < L.length := by omega
  have h1 := hget (36 * i + e) (by rw [List.length_map]; omega)
  rw [Nat.zero_add, getElem!_pos _ _ (by rw [List.length_map]; exact hm), List.getElem_map] at h1
  rw [syl3ArrOfChars, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, dif_pos he,
    Option.getD_some, getD_decM he, ln_slot he, hs, String.toList_ofList,
    Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_eq_getElem hm,
    Option.getD_some, syl3Digit, h1]

theorem mats_eq (i : Fin 81) : syl3MatsArr.getD i.val #[] = decM (slot MP i.val) := by
  simp only [syl3MatsArr]
  rw [tabulate_getD]
  exact arrOfChars_eq MS.eq codesM (by omega)

theorem gens_eq (k : Fin 4) : syl3GenArr.getD k.val #[] = decM (slot GP k.val) := by
  simp only [syl3GenArr]
  rw [tabulate_getD]
  exact arrOfChars_eq GS.eq codesG (by omega)

theorem tab_eq {m : ℕ} (hm : m < 324) : (syl3TabArr.getD m 0).val = ln7 TB m := by
  have h := congrArg (fun L : List ℕ => L[m]?) (beq_iff_eq.1 tabB)
  simp only [List.getElem?_map, List.getElem?_range hm, Option.map_some] at h
  rw [Array.getD_eq_getD_getElem?, ← Array.getElem?_toList]
  cases hx : syl3TabArr.toList[m]? with
  | none =>
    rw [hx] at h
    simp at h
  | some x =>
    rw [hx] at h
    simp only [Option.map_some, Option.some.injEq] at h
    simpa using h

theorem rf_eq {s : ℕ} (hs : s < 6) : decM (getL 0 RF s) = syl3ReflArr s := by
  have h := List.all_eq_true.1 rfB s (List.mem_range.2 hs)
  apply arr_eq_of_getD (size_decM _) (by simp [syl3ReflArr])
  intro e he
  rw [getD_decM he]
  exact (of_decide_eq_true (List.all_eq_true.1 h e (List.mem_range.2 he))).symm

theorem one_eq : decM ONE = syl3OneArr := by
  apply arr_eq_of_getD (size_decM _) (by simp [syl3OneArr])
  intro e he
  rw [getD_decM he]
  exact (of_decide_eq_true (List.all_eq_true.1 oneB e (List.mem_range.2 he))).symm

theorem word_eq (j : Fin 81) : syl3GenWordArr.getD j.val [] = syl3GenWordData.getD j.val [] := by
  rw [syl3GenWordArr, tabulate_getD]
  rfl

theorem word_succ {j : ℕ} (hj : j < 81) (h0 : j ≠ 0) (hl : getL 0 WL j < 4) :
    syl3GenWordData.getD j [] = syl3GenWordData.getD (getL 0 WP j) [] ++ [⟨getL 0 WL j, hl⟩] := by
  have h := wordsB
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq] at h
  rcases h.2 j hj with h1 | h1
  · exact absurd h1 h0
  · apply List.map_injective_iff.2 Fin.val_injective
    rw [h1, List.map_append]
    rfl

theorem mul_eq : ∀ (j i : Fin 81),
    (syl3MulIdxW syl3TabArr syl3GenWordArr i j).val = mulK MT i.val j.val := by
  intro ⟨j, hj⟩
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro i
    have hmt := allN_true (allN_true mt i.2) hj
    by_cases h0 : j = 0
    · subst h0
      change Nat.beq (ln7 MT (Nat.mul 81 i.val)) i.val = true at hmt
      have hw : syl3GenWordArr.getD 0 [] = [] := by rw [word_eq ⟨0, by norm_num⟩]; rfl
      simp only [syl3MulIdxW, hw, List.foldl_nil]
      exact (Nat.eq_of_beq_eq_true hmt).symm
    · have hb : Nat.beq j 0 = false := by rw [nb]; simp [h0]
      rw [hb] at hmt
      change bAnd(Nat.blt (getL 0 WP j) j, bAnd(Nat.blt (getL 0 WL j) 4,
        Nat.beq (ln7 MT (Nat.add (Nat.mul 81 i.val) j))
          (ln7 TB (Nat.add (Nat.mul 4 (ln7 MT (Nat.add (Nat.mul 81 i.val) (getL 0 WP j))))
            (getL 0 WL j))))) = true at hmt
      simp only [bAnd_eq, Bool.and_eq_true, Nat.blt_eq] at hmt
      obtain ⟨hp, hl, hv⟩ := hmt
      have hv := Nat.eq_of_beq_eq_true hv
      have hw := word_succ hj h0 hl
      have hpj : getL 0 WP j < 81 := by omega
      have hih := ih _ hp hpj i
      have hw' : syl3GenWordArr.getD j [] =
          syl3GenWordArr.getD (getL 0 WP j) [] ++ [⟨getL 0 WL j, hl⟩] := by
        rw [word_eq ⟨j, hj⟩, word_eq ⟨_, hpj⟩]
        exact hw
      simp only [syl3MulIdxW] at hih ⊢
      rw [hw', List.foldl_append, List.foldl_cons, List.foldl_nil, syl3TabW,
        tab_eq (by omega), hih]
      exact hv.symm

theorem pow_eq (i : Fin 81) (a : Fin 3) :
    (syl3PowIdxW syl3TabArr syl3GenWordArr i a).val = powK MT i.val a.val := by
  fin_cases a <;> simp [syl3PowIdxW, powK, nIf_eq, nb, mul_eq]

theorem deq {a b : Fin 81} {x y : ℕ} (h : a.val = x) (h' : b.val = y) :
    decide (a = b) = decide (x = y) :=
  decide_eq_decide.2 (by rw [Fin.ext_iff, h, h'])

theorem dne {a b : Fin 81} {x y : ℕ} (h : a.val = x) (h' : b.val = y) :
    decide (a ≠ b) = !decide (x = y) := by
  rw [← decide_not]
  exact decide_eq_decide.2 (by rw [Ne, Fin.ext_iff, h, h'])

theorem ord3_eq (i : Fin 81) : syl3Ord3W syl3TabArr syl3GenWordArr i = ord3K MT i.val := by
  unfold syl3Ord3W ord3K
  rw [bAnd_eq, notB_eq, nb, nb, dne rfl rfl, deq (by rw [mul_eq, mul_eq]) rfl]
  rfl

theorem comm_eq (i j : Fin 81) : syl3CommW syl3TabArr syl3GenWordArr i j = commK MT i.val j.val := by
  simp [syl3CommW, commK, nb, Fin.ext_iff, mul_eq]

theorem indep_eq (i j : Fin 81) :
    syl3IndepW syl3TabArr syl3GenWordArr i j = indepK MT i.val j.val := by
  unfold syl3IndepW indepK
  rw [bAnd_eq, bAnd_eq, notB_eq, notB_eq, notB_eq, nb, nb, nb, Bool.and_assoc, dne rfl rfl,
    dne rfl rfl, dne rfl (mul_eq i i)]
  rfl

theorem out_eq (i j k : Fin 81) :
    syl3OutW syl3TabArr syl3GenWordArr i j k = outK MT i.val j.val k.val := by
  apply Bool.eq_iff_iff.2
  simp only [syl3OutW, outK, List.all_eq_true, List.mem_finRange, true_implies, notB_eq, nb,
    decide_eq_true_eq, CFSG.KC.Misc.ArrEnum.allNP_iff, Bool.not_eq_true', decide_eq_false_iff_not,
    ne_eq, Fin.ext_iff, mul_eq, pow_eq]
  constructor
  · intro h a ha b hb
    exact h ⟨a, ha⟩ ⟨b, hb⟩
  · intro h a b
    exact h a.val a.2 b.val b.2

theorem fm_spec {i n : ℕ} (hi : i < 81) (hn : n < 729) :
    fixP (slot MP i) n = (getL 0 FM i).testBit n := by
  have h := allN_true fm hi
  rw [strictB_eq, strictB_eq] at h
  have h2 := allN_true (allN_true h (by omega : n / 27 < 27)) (by omega : n % 27 < 27)
  rw [strictB_eq] at h2
  have hn' : Nat.add (Nat.mul 27 (n / 27)) (n % 27) = n := Nat.div_add_mod n 27
  rw [hn', beq_land_one] at h2
  cases hb : (getL 0 FM i).testBit n <;> cases hf : fixP (slot MP i) n <;>
    simp_all [notB_eq]

theorem fixArr_mats (j : Fin 81) {n : ℕ} (hn : n < 729) :
    syl3FixArr (syl3MatsArr.getD j.val #[]) (syl3VecArr n) = (getL 0 FM j).testBit n := by
  rw [mats_eq, fixArr_decM, fm_spec j.2 hn]

theorem fixList_eq (i : Fin 81) :
    (syl3FixCodesW syl3MatsArr).getD i.val [] = (List.range 729).filter fun n =>
      (getL 0 FM i).testBit n := by
  rw [syl3FixCodesW, tabulate_getD]
  exact List.filter_congr fun n hn => fixArr_mats i (List.mem_range.1 hn)

theorem filter_range_testBit (x y : ℕ) (L : List ℕ) (hL : ∀ n ∈ L, n < 729) (j : Fin 81)
    (h : L = (List.range 729).filter fun n => x.testBit n)
    (hy : y = Nat.land x (getL 0 FM j)) :
    L.filter (fun n => syl3FixArr (syl3MatsArr.getD j.val #[]) (syl3VecArr n)) =
      (List.range 729).filter fun n => y.testBit n := by
  rw [List.filter_congr fun n hn => fixArr_mats j (hL n hn), h, List.filter_filter]
  refine List.filter_congr fun n _ => ?_
  rw [hy]
  change _ = (x &&& getL 0 FM j).testBit n
  rw [Nat.testBit_and, Bool.and_comm]

theorem len2 (i j : Fin 81) :
    (((syl3FixCodesW syl3MatsArr).getD i.val []).filter fun n =>
      syl3FixArr (syl3MatsArr.getD j.val #[]) (syl3VecArr n)).length =
      cntK (Nat.land (getL 0 FM i) (getL 0 FM j)) 729 := by
  rw [filter_range_testBit (getL 0 FM i) _ _ (fun n hn => by
      rw [fixList_eq] at hn
      exact List.mem_range.1 (List.mem_filter.1 hn).1) j (fixList_eq i) rfl,
    length_filter_testBit]

theorem len3 (i j k : Fin 81) :
    ((((syl3FixCodesW syl3MatsArr).getD i.val []).filter fun n =>
      syl3FixArr (syl3MatsArr.getD j.val #[]) (syl3VecArr n)).filter fun n =>
        syl3FixArr (syl3MatsArr.getD k.val #[]) (syl3VecArr n)).length =
      cntK (Nat.land (Nat.land (getL 0 FM i) (getL 0 FM j)) (getL 0 FM k)) 729 := by
  have h2 := filter_range_testBit (getL 0 FM i) _ _ (fun n hn => by
      rw [fixList_eq] at hn
      exact List.mem_range.1 (List.mem_filter.1 hn).1) j (fixList_eq i) rfl
  rw [h2, filter_range_testBit (Nat.land (getL 0 FM i) (getL 0 FM j)) _ _
    (fun n hn => List.mem_range.1 (List.mem_filter.1 hn).1) k rfl rfl, length_filter_testBit]

theorem p12_facts {i j : ℕ} (hi : i < 81) (hj : j < 81) (h1 : ord3K MT i = true)
    (h2 : ord3K MT j = true) (h3 : commK MT i j = true) (h4 : indepK MT i j = true) :
    cntK (Nat.land (getL 0 FM i) (getL 0 FM j)) 729 ≤ 9 ∧
      ∀ k < 81, ord3K MT k = true → commK MT i k = true → commK MT j k = true →
        outK MT i j k = true →
          cntK (Nat.land (Nat.land (getL 0 FM i) (getL 0 FM j)) (getL 0 FM k)) 729 ≤ 3 := by
  have h := allN_true p12 hi
  simp only [bIf_eq_true', h1, Bool.not_true, Bool.false_or, strictB_eq] at h
  have h' := allN_true h hj
  simp only [bIf_eq_true', bAnd_eq, h2, h3, h4, Bool.and_true, Bool.not_true, Bool.false_or,
    strictB_eq, Bool.and_eq_true, Nat.ble_eq] at h'
  refine ⟨h'.1, fun k hk g1 g2 g3 g4 => ?_⟩
  have h'' := allN_true h'.2 hk
  simp only [bIf_eq_true', bAnd_eq, g1, g2, g3, g4, Bool.and_true, Bool.not_true, Bool.false_or,
    Nat.ble_eq] at h''
  exact h''

theorem gen_true : syl3CheckGen syl3GenArr = true := by
  rw [syl3CheckGen, List.all_eq_true]
  intro k _
  refine decide_eq_true ?_
  rw [gens_eq]
  have h := allN_true gen k.2
  rw [bAnd_eq, Bool.and_eq_true] at h
  have hc := decM_of_chainK _ _ h.2
  rw [Nat.eq_of_beq_eq_true h.1] at hc
  have hsw : getL [] SW k.val = (syl3SimpleWord k).map Fin.val := by
    rw [getL_eq_getD, ← beq_iff_eq.1 swB, syl3SimpleWord, List.getD_eq_getElem?_getD,
      List.getD_eq_getElem?_getD, List.getElem?_map]
    cases syl3SimpleWordData[k.val]? <;> rfl
  rw [hc, hsw, List.foldr_map, one_eq]
  refine congrArg (fun f => List.foldr f syl3OneArr (syl3SimpleWord k)) ?_
  funext s M
  rw [rf_eq s.2]

theorem elt_true :
    syl3CheckElt syl3GenArr syl3MatsArr syl3GenWordArr = true := by
  rw [syl3CheckElt, List.all_eq_true]
  intro i _
  refine decide_eq_true ?_
  rw [mats_eq, word_eq]
  have h := allN_true elt i.2
  rw [bAnd_eq, Bool.and_eq_true] at h
  have hc := decM_of_chainK _ _ h.2
  rw [Nat.eq_of_beq_eq_true h.1] at hc
  have hw : getL [] (syl3GenWordData.map (List.map Fin.val)) i.val =
      (syl3GenWordData.getD i.val []).map Fin.val := by
    rw [getL_eq_getD, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
    cases syl3GenWordData[i.val]? <;> rfl
  rw [hc, hw, List.foldr_map, one_eq]
  refine congrArg (fun f => List.foldr f syl3OneArr (syl3GenWordData.getD i.val [])) ?_
  funext k M
  have hg : getL 0 ((List.range 4).map (slot GP)) k.val = slot GP k.val := by
    rw [getL_eq_getD]
    simp [List.getD_eq_getElem?_getD, List.getElem?_range k.2]
  rw [hg, gens_eq]

theorem tab_true : syl3CheckTab syl3GenArr syl3MatsArr syl3TabArr = true := by
  rw [syl3CheckTab, List.all_eq_true]
  intro i _
  rw [List.all_eq_true]
  intro k _
  rw [decide_eq_true_iff, mats_eq, gens_eq, mats_eq]
  have h := allN_true tab i.2
  rw [strictB_eq] at h
  have h2 := allN_true h k.2
  rw [strictB_eq, bAnd_eq, Bool.and_eq_true] at h2
  have ht : (syl3TabW syl3TabArr i k).val = ln7 TB (Nat.add (Nat.mul 4 i.val) k.val) := by
    rw [syl3TabW]
    exact tab_eq (by omega)
  rw [ht]
  exact mulArr_of_prodOK h2.2

theorem inv_true : syl3CheckInv syl3GenArr = true := by
  have h := inv
  simp only [invK, bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨h0, h1, h2, h3⟩ := h
  rw [syl3CheckInv, List.all_eq_true]
  intro k _
  rw [decide_eq_true_iff, gens_eq, gens_eq, ← one_eq]
  fin_cases k
  · exact mulArr_of_prodOK h0
  · exact mulArr_of_prodOK h1
  · exact mulArr_of_prodOK h2
  · exact mulArr_of_prodOK h3

theorem dist_true : syl3CheckDistinct syl3MatsArr = true := by
  rw [syl3CheckDistinct, List.all_eq_true]
  intro i _
  rw [List.all_eq_true]
  intro j _
  rw [Bool.or_eq_true]
  by_cases hij : i = j
  · exact Or.inl (decide_eq_true hij)
  · right
    have h := allN_true dist i.2
    rw [strictB_eq] at h
    have h2 := allN_true h j.2
    have hb : Nat.beq i.val j.val = false := by
      rw [nb]
      simpa [Fin.ext_iff] using hij
    rw [hb, strictB_eq] at h2
    obtain ⟨e, he, hne⟩ := anyN_true h2
    rw [notB_eq, Bool.not_eq_true', nb, decide_eq_false_iff_not] at hne
    rw [List.any_eq_true]
    refine ⟨e, List.mem_range.2 he, decide_eq_true ?_⟩
    rw [mats_eq, mats_eq, getD_decM he, getD_decM he]
    intro hc
    exact hne (by exact_mod_cast sub_left_injective hc)

theorem nonab_true : syl3CheckNonab syl3TabArr syl3GenWordArr = true := by
  rw [syl3CheckNonab, List.any_eq_true]
  refine ⟨1, List.mem_finRange _, List.any_eq_true.2 ⟨3, List.mem_finRange _, ?_⟩⟩
  rw [comm_eq]
  change (!(Nat.beq (mulK MT 1 3) (mulK MT 3 1))) = true
  rw [nonab]
  rfl

theorem p1_true : syl3CheckP1 syl3TabArr syl3GenWordArr syl3MatsArr (syl3FixCodesW syl3MatsArr) =
    true := by
  rw [syl3CheckP1, List.all_eq_true]
  intro i _
  rw [Bool.or_eq_true, ord3_eq, Bool.not_eq_true']
  by_cases h1 : ord3K MT i.val = true
  · right
    rw [List.all_eq_true]
    intro j _
    rw [Bool.or_eq_true, Bool.not_eq_true', ord3_eq, comm_eq, indep_eq, len2]
    by_cases hg : (ord3K MT j.val && commK MT i.val j.val && indepK MT i.val j.val) = true
    · simp only [Bool.and_eq_true] at hg
      exact Or.inr (decide_eq_true (p12_facts i.2 j.2 h1 hg.1.1 hg.1.2 hg.2).1)
    · exact Or.inl (by simpa using hg)
  · exact Or.inl (by simpa using h1)

theorem p2_true : syl3CheckP2 syl3TabArr syl3GenWordArr syl3MatsArr (syl3FixCodesW syl3MatsArr) =
    true := by
  rw [syl3CheckP2, List.all_eq_true]
  intro i _
  rw [Bool.or_eq_true, ord3_eq, Bool.not_eq_true']
  by_cases h1 : ord3K MT i.val = true
  · right
    rw [List.all_eq_true]
    intro j _
    rw [Bool.or_eq_true, Bool.not_eq_true', ord3_eq, comm_eq, indep_eq]
    by_cases hg : (ord3K MT j.val && commK MT i.val j.val && indepK MT i.val j.val) = true
    · simp only [Bool.and_eq_true] at hg
      have hf := (p12_facts i.2 j.2 h1 hg.1.1 hg.1.2 hg.2).2
      right
      rw [List.all_eq_true]
      intro k _
      rw [Bool.or_eq_true, Bool.not_eq_true', ord3_eq, comm_eq, comm_eq, out_eq, len3]
      by_cases hk : (ord3K MT k.val && commK MT i.val k.val && commK MT j.val k.val &&
          outK MT i.val j.val k.val) = true
      · simp only [Bool.and_eq_true] at hk
        exact Or.inr (decide_eq_true (hf k.val k.2 hk.1.1.1 hk.1.1.2 hk.1.2 hk.2))
      · exact Or.inl (by simpa using hk)
    · exact Or.inl (by simpa using hg)
  · exact Or.inl (by simpa using h1)

theorem syl3Check_true : syl3Check () = true := by
  simp only [syl3Check, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨gen_true, elt_true⟩, tab_true⟩, inv_true⟩, dist_true⟩, nonab_true⟩, p1_true⟩,
    p2_true⟩

end CFSG.KD.Syl3W

end
