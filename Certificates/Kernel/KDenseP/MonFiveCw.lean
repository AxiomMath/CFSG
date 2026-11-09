module

public import Certificates.Kernel.KDenseP.MonFiveNorm
import CFSG.Certificates.Kernel.Common.Harness

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CertificateChecks.KernelKDenseP.MonFive

open CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.Griess CFSG.Monster.Generated
  CFSG.AGLEmbedding.Norton.MON5_7
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFive CFSG.KC.PcCollect CFSG.KC.KDenseP.MonFive

set_option maxRecDepth 100000

@[expose] def cwPair (i j : ℕ) : List Native.Gen × List Native.Gen :=
  (fiveGens[j]! ++ fiveGens[i]!, fiveGens[i]! ++ rhsW fiveCw[i * 9 + j]!)

theorem agreeAll_app {l l' : List (List Native.Gen × List Native.Gen)} (h : agreeAll l = true)
    (h' : agreeAll l' = true) : agreeAll (l ++ l') = true := by
  simp only [agreeAll, List.all_append, Bool.and_eq_true] at *
  exact ⟨h, h'⟩

theorem agreeAll_left {l l' : List (List Native.Gen × List Native.Gen)}
    (h : agreeAll (l ++ l') = true) : agreeAll l = true := by
  simp only [agreeAll, List.all_append, Bool.and_eq_true] at *
  exact h.1

theorem agreeAll_right {l l' : List (List Native.Gen × List Native.Gen)}
    (h : agreeAll (l ++ l') = true) : agreeAll l' = true := by
  simp only [agreeAll, List.all_append, Bool.and_eq_true] at *
  exact h.2

theorem relDrop_ok {a b : ℕ} (h1 : agreeAll (relSeg a b) = true)
    (h2 : agreeAll (relEqs.drop (a + b)) = true) : agreeAll (relEqs.drop a) = true := by
  rw [← List.take_append_drop b (relEqs.drop a), List.drop_drop]
  exact agreeAll_app h1 h2

theorem relSeg_add (a b c : ℕ) : relSeg a (b + c) = relSeg a b ++ relSeg (a + b) c := by
  unfold relSeg
  rw [List.take_add, List.drop_drop]

theorem powEqs_length : powEqs.length = 27 := by decide +kernel

theorem pwEqs_length : pwEqs.length = 9 := by simp [pwEqs]

theorem cwEqs_eq : cwEqs = (List.range' 1 8).map (cwPair 0) ++
    (List.range' 1 8).flatMap fun i => ((List.range 9).filter (i < ·)).map (cwPair i) := by
  have e1 : List.range 9 = 0 :: List.range' 1 8 := by decide
  have e2 : (List.range 9).filter (0 < ·) = List.range' 1 8 := by decide
  unfold cwEqs
  rw [e1, List.flatMap_cons, ← e1, e2]
  rfl

theorem relEqs_drop27 : relEqs.drop 27 = pwEqs ++ cwEqs := by
  unfold relEqs
  rw [List.append_assoc, List.drop_left' powEqs_length]

theorem relEqs_drop36 : relEqs.drop 36 = cwEqs := by
  have e : relEqs.drop 36 = (relEqs.drop 27).drop 9 := by rw [List.drop_drop]
  rw [e, relEqs_drop27, List.drop_left' pwEqs_length]

theorem relSeg_pow : relSeg 0 27 = powEqs := by
  unfold relSeg relEqs
  rw [List.drop_zero, List.append_assoc, List.take_left' powEqs_length]

theorem relSeg_pw : relSeg 27 9 = pwEqs := by
  unfold relSeg
  rw [relEqs_drop27, List.take_left' pwEqs_length]

theorem relSeg_cw0 (d b : ℕ) (h : d + b ≤ 8) :
    relSeg (36 + d) b = (List.range' (1 + d) b).map (cwPair 0) := by
  unfold relSeg
  have e : relEqs.drop (36 + d) = (relEqs.drop 36).drop d := by rw [List.drop_drop]
  rw [e, relEqs_drop36, cwEqs_eq, List.drop_append_of_le_length (by simp; omega),
    List.take_append_of_le_length (by simp; omega)]
  apply List.ext_getElem
  · simp
    omega
  · intro i h1 h2
    simp only [List.getElem_take, List.getElem_drop, List.getElem_map, List.getElem_range']
    congr 1
    omega

theorem relDrop44 : relEqs.drop 44 =
    (List.range' 1 8).flatMap fun i => ((List.range 9).filter (i < ·)).map (cwPair i) := by
  have e : relEqs.drop 44 = (relEqs.drop 36).drop 8 := by rw [List.drop_drop]
  rw [e, relEqs_drop36, cwEqs_eq, List.drop_left' (by simp)]

theorem cwPair_mem (k m : ℕ) (hk : 1 ≤ k) (hkm : k < m) (hm : m < 9) : cwPair k m ∈ relEqs.drop 44 := by
  rw [relDrop44]
  exact List.mem_flatMap.2 ⟨k, List.mem_range'_1.2 ⟨hk, by omega⟩,
    List.mem_map.2 ⟨m, List.mem_filter.2 ⟨List.mem_range.2 hm, by simpa using hkm⟩, rfl⟩⟩

theorem cw_rel_of_agree (hpow : agreeAll powEqs = true) {i m : ℕ} (hi : i < 9) (hm : m < 9)
    (h : agree (cwPair i m).1 (cwPair i m).2 = true) :
    x5 i * x5 m = evW x5 (cF i m) * x5 i := by
  have e : gw (fiveGens[m]! ++ fiveGens[i]!) = gw (fiveGens[i]! ++ rhsW fiveCw[i * 9 + m]!) :=
    agree_sound h
  simp only [gw_append] at e
  have hc : cF i m = nfFrom 0 (fiveCw[i * 9 + m]!).toList := rfl
  rw [hc, ← gw_rhsW_ev hpow _ (cw_size _ (by omega))]
  exact e

section Facts

variable (hpow : agreeAll powEqs = true) (hpw : agreeAll pwEqs = true)
  (hrest : agreeAll (relEqs.drop 44) = true)

include hpow hrest in
theorem hC1 : ∀ k m, 1 ≤ k → k < m → m < 9 → x5 k * x5 m = evW x5 (cF k m) * x5 k :=
  fun k m hk hkm hm => cw_rel_of_agree hpow (by omega) hm (agree_of_mem hrest (cwPair_mem k m hk hkm hm))

include hpow hpw hrest in
theorem hD1 : ∀ k j, 1 ≤ k → k < j → j < 9 → x5 j * x5 k = x5 k * evW x5 (dT T5 9 k j) :=
  conjD_of_checks x5 9 T5 P5 1 cF (hC1 hpow hrest) (fun k m _ h1 h2 => cF_lt k (by omega) m h2 h1)
    (fun k j _ h1 h2 => dT_lt k (by omega) j h2 h1)
    (fun k _ hk => by rw [pT_eq k hk]; exact hPw hpow hpw k hk)
    (fun k _ hk => by rw [pT_eq k hk]; exact pF_lt k hk) (fun k j _ h1 h2 => dchk k (by omega) j h2 h1)

include hpow hpw hrest in
theorem col1 {l l' : List ℕ} (hl : ∀ j ∈ l, 1 ≤ j ∧ j < 9) (hl' : ∀ j ∈ l', 1 ≤ j ∧ j < 9)
    (h : colE 9 T5 P5 l l' = true) : evW x5 l = evW x5 l' :=
  colE_sound x5 9 T5 P5 1 (hD1 hpow hpw hrest) (fun k j _ h1 h2 => dT_lt k (by omega) j h2 h1)
    (fun k _ hk => by rw [pT_eq k hk]; exact hPw hpow hpw k hk)
    (fun k _ hk => by rw [pT_eq k hk]; exact pF_lt k hk) hl hl' h

theorem flat0_lt : ∀ l : List ℕ, (∀ m ∈ l, 1 ≤ m ∧ m < 9) → ∀ a ∈ l.flatMap (cF 0), 1 ≤ a ∧ a < 9 := by
  intro l hl a ha
  obtain ⟨m, hm, ha'⟩ := List.mem_flatMap.1 ha
  have := cF_lt 0 (by norm_num) m (hl m hm).2 (by have := (hl m hm).1; omega) a ha'
  omega

include hpow hrest in
theorem rel_cw1 (a b : ℕ) (ha : 1 ≤ a) (hab : a < b) (hb : b < 9) :
    evW x5 [a, b] = evW x5 (cF a b ++ [a]) := by
  rw [evW_append, evW_cons, evW_cons, evW_cons, evW_nil, mul_one, mul_one,
    hC1 hpow hrest a b ha hab hb]

include hpow hpw hrest in
theorem step0 (k e e' : ℕ) (lw L1 L2 : List ℕ) (hk : 1 ≤ k) (hk9 : k < 9)
    (hrelw : evW x5 lw = evW x5 (L1 ++ List.replicate e k ++ L2))
    (hK : ∀ m ∈ lw ++ L1 ++ L2, x5 0 * x5 m = evW x5 (cF 0 m) * x5 0)
    (hlet : ∀ m ∈ lw ++ L1 ++ L2, 1 ≤ m ∧ m < 9)
    (hc : colE 9 T5 P5 (lw.flatMap (cF 0))
      (L1.flatMap (cF 0) ++ (List.replicate e k).flatMap (cF 0) ++ L2.flatMap (cF 0)) = true)
    (hc5 : colE 9 T5 P5 ((List.replicate 5 k).flatMap (cF 0)) [] = true)
    (hpk : pF k = []) (hee : (e * e') % 5 = 1) :
    x5 0 * x5 k = evW x5 (cF 0 k) * x5 0 := by
  have hl1 : ∀ m ∈ lw, 1 ≤ m ∧ m < 9 := fun m hm => hlet m (by simp [hm])
  have hl2 : ∀ m ∈ L1, 1 ≤ m ∧ m < 9 := fun m hm => hlet m (by simp [hm])
  have hl3 : ∀ m ∈ L2, 1 ≤ m ∧ m < 9 := fun m hm => hlet m (by simp [hm])
  have hl4 : ∀ m ∈ List.replicate e k, 1 ≤ m ∧ m < 9 := fun m hm => by
    rw [(List.mem_replicate.1 hm).2]
    exact ⟨hk, hk9⟩
  refine image_of_rel x5 k e e' lw L1 L2 hrelw hK
    (col1 hpow hpw hrest (flat0_lt lw hl1) ?_ hc) (by rw [hPw hpow hpw k hk9, hpk]; rfl) ?_ hee
  · intro a ha
    simp only [List.mem_append] at ha
    rcases ha with (ha | ha) | ha
    · exact flat0_lt L1 hl2 a ha
    · exact flat0_lt _ hl4 a ha
    · exact flat0_lt L2 hl3 a ha
  · rw [← evW_flatMap_replicate x5 5 k]
    exact col1 hpow hpw hrest (flat0_lt _ fun m hm => by rw [(List.mem_replicate.1 hm).2]; exact ⟨hk, hk9⟩)
      (by simp) hc5

include hpow hpw hrest in
theorem im0_all (h1 : agree (cwPair 0 1).1 (cwPair 0 1).2 = true)
    (h4 : agree (cwPair 0 4).1 (cwPair 0 4).2 = true) (h5 : agree (cwPair 0 5).1 (cwPair 0 5).2 = true)
    (h6 : agree (cwPair 0 6).1 (cwPair 0 6).2 = true) :
    ∀ m, 1 ≤ m → m < 9 → x5 0 * x5 m = evW x5 (cF 0 m) * x5 0 := by
  have K0 : ∀ m ∈ [1, 4, 5, 6], x5 0 * x5 m = evW x5 (cF 0 m) * x5 0 := by
    intro m hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl
    · exact cw_rel_of_agree hpow (by norm_num) (by norm_num) h1
    · exact cw_rel_of_agree hpow (by norm_num) (by norm_num) h4
    · exact cw_rel_of_agree hpow (by norm_num) (by norm_num) h5
    · exact cw_rel_of_agree hpow (by norm_num) (by norm_num) h6
  have h8 := step0 hpow hpw hrest 8 1 1 [4, 6] [6] [4] (by norm_num) (by norm_num)
    ((rel_cw1 hpow hrest 4 6 (by norm_num) (by norm_num) (by norm_num)).trans
      (congrArg (evW x5) (by decide +kernel : cF 4 6 ++ [4] = [6] ++ List.replicate 1 8 ++ [4])))
    (fun m hm => K0 m (by revert m hm; decide))
    (by decide)
    (by quickRfl) (by quickRfl) (by decide +kernel) (by norm_num)
  have K1 := forall_mem_cons' (P := fun m => x5 0 * x5 m = evW x5 (cF 0 m) * x5 0) h8 K0
  have h2 := step0 hpow hpw hrest 2 2 3 [1, 5] [] [6, 6, 8, 1] (by norm_num) (by norm_num)
    ((rel_cw1 hpow hrest 1 5 (by norm_num) (by norm_num) (by norm_num)).trans
      (congrArg (evW x5) (by decide +kernel : cF 1 5 ++ [1] = [] ++ List.replicate 2 2 ++ [6, 6, 8, 1])))
    (fun m hm => K1 m (by revert m hm; decide))
    (by decide)
    (by quickRfl) (by quickRfl) (by decide +kernel) (by norm_num)
  have K2 := forall_mem_cons' (P := fun m => x5 0 * x5 m = evW x5 (cF 0 m) * x5 0) h2 K1
  have h3 := step0 hpow hpw hrest 3 4 4 [1, 6] [] [4, 4, 4, 4, 5, 6, 6, 6, 1] (by norm_num) (by norm_num)
    ((rel_cw1 hpow hrest 1 6 (by norm_num) (by norm_num) (by norm_num)).trans
      (congrArg (evW x5) (by decide +kernel : cF 1 6 ++ [1] = [] ++ List.replicate 4 3 ++ [4, 4, 4, 4, 5, 6, 6, 6, 1])))
    (fun m hm => K2 m (by revert m hm; decide))
    (by decide)
    (by quickRfl) (by quickRfl) (by decide +kernel) (by norm_num)
  have K3 := forall_mem_cons' (P := fun m => x5 0 * x5 m = evW x5 (cF 0 m) * x5 0) h3 K2
  have h7 := step0 hpow hpw hrest 7 4 4 [1, 3] [2, 2, 2, 3, 3, 3, 4, 4, 4, 5] [8, 8, 8, 8, 1] (by norm_num) (by norm_num)
    ((rel_cw1 hpow hrest 1 3 (by norm_num) (by norm_num) (by norm_num)).trans
      (congrArg (evW x5) (by decide +kernel : cF 1 3 ++ [1] = [2, 2, 2, 3, 3, 3, 4, 4, 4, 5] ++ List.replicate 4 7 ++ [8, 8, 8, 8, 1])))
    (fun m hm => K3 m (by revert m hm; decide))
    (by decide)
    (by quickRfl) (by quickRfl) (by decide +kernel) (by norm_num)
  have K4 := forall_mem_cons' (P := fun m => x5 0 * x5 m = evW x5 (cF 0 m) * x5 0) h7 K3
  intro m hm hm9
  exact K4 m (by interval_cases m <;> simp)

include hpow hpw hrest in
theorem cw0_wordLin (h1 : agree (cwPair 0 1).1 (cwPair 0 1).2 = true)
    (h4 : agree (cwPair 0 4).1 (cwPair 0 4).2 = true) (h5 : agree (cwPair 0 5).1 (cwPair 0 5).2 = true)
    (h6 : agree (cwPair 0 6).1 (cwPair 0 6).2 = true) {l : List ℕ} (hl : ∀ m ∈ l, 1 ≤ m ∧ m < 9) :
    agreeAll (l.map (cwPair 0)) = true := by
  refine CertificateChecks.KernelKDenseP.agreeAll_of_wordLin (fun p hp => ?_) (fun p hp => ?_)
  · obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hp
    refine ⟨fun g hg => ?_, fun g hg => ?_⟩
    · rcases List.mem_append.1 hg with hg | hg
      · exact gens_valid hpw m (hl m hm).2 g hg
      · exact gens_valid hpw 0 (by norm_num) g hg
    · rcases List.mem_append.1 hg with hg | hg
      · exact gens_valid hpw 0 (by norm_num) g hg
      · exact rhsW_valid hpow hpw _ g hg
  · obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hp
    have hg : gw (cwPair 0 m).1 = gw (cwPair 0 m).2 := by
      change gw (fiveGens[m]! ++ fiveGens[0]!) = gw (fiveGens[0]! ++ rhsW fiveCw[0 * 9 + m]!)
      simp only [gw_append]
      rw [gw_rhsW_ev hpow _ (cw_size _ (by have := (hl m hm).2; omega))]
      exact im0_all hpow hpw hrest h1 h4 h5 h6 m (hl m hm).1 (hl m hm).2
    exact congrArg Subtype.val hg

end Facts

theorem pow_of (h0 : agreeAll (relSeg 0 13) = true) (h1 : agreeAll (relSeg 13 12) = true)
    (h2 : agreeAll (relSeg 25 10) = true) : agreeAll powEqs = true := by
  rw [← relSeg_pow, relSeg_add 0 13 14, relSeg_add 13 12 2]
  refine agreeAll_app h0 (agreeAll_app h1 ?_)
  rw [relSeg_add 25 2 8] at h2
  exact agreeAll_left h2

theorem pw_of (h2 : agreeAll (relSeg 25 10) = true) (hA : agreeAll (relSeg 35 2 ++ relSeg 39 2) = true) :
    agreeAll pwEqs = true := by
  rw [← relSeg_pw, relSeg_add 27 8 1]
  rw [relSeg_add 25 2 8] at h2
  have hA' := agreeAll_left hA
  rw [relSeg_add 35 1 1] at hA'
  exact agreeAll_app (agreeAll_right h2) (agreeAll_left hA')

theorem rest_of (hB : agreeAll (relSeg 41 1 ++ relSeg 44 3) = true) (h4 : agreeAll (relSeg 47 10) = true)
    (h5 : agreeAll (relSeg 57 11) = true) (h6 : agreeAll (relTail 68) = true) :
    agreeAll (relEqs.drop 44) = true :=
  relDrop_ok (a := 44) (b := 3) (agreeAll_right hB)
    (relDrop_ok (a := 47) (b := 10) h4 (relDrop_ok (a := 57) (b := 11) h5 h6))

theorem one_agree {l : List (List Native.Gen × List Native.Gen)} {p : List Native.Gen × List Native.Gen}
    (h : agreeAll l = true) (hl : l = [p]) : agree p.1 p.2 = true :=
  agree_of_mem h (by rw [hl]; exact List.mem_singleton_self p)

theorem relSeg35_ok (h0 : agreeAll (relSeg 0 13) = true) (h1 : agreeAll (relSeg 13 12) = true)
    (h2 : agreeAll (relSeg 25 10) = true) (hA : agreeAll (relSeg 35 2 ++ relSeg 39 2) = true)
    (hB : agreeAll (relSeg 41 1 ++ relSeg 44 3) = true) (h4 : agreeAll (relSeg 47 10) = true)
    (h5 : agreeAll (relSeg 57 11) = true) (h6 : agreeAll (relTail 68) = true) :
    agreeAll (relSeg 35 6) = true ∧ agreeAll (relSeg 41 6) = true := by
  have hpow := pow_of h0 h1 h2
  have hpw := pw_of h2 hA
  have hrest := rest_of hB h4 h5 h6
  have hA1 := agreeAll_left hA
  have hA2 := agreeAll_right hA
  have hB1 := agreeAll_left hB
  rw [relSeg_add 35 1 1] at hA1
  have e1 : relSeg 36 1 = [cwPair 0 1] := relSeg_cw0 0 1 (by norm_num)
  have e45 : relSeg 39 2 = [cwPair 0 4, cwPair 0 5] := relSeg_cw0 3 2 (by norm_num)
  have e6 : relSeg 41 1 = [cwPair 0 6] := relSeg_cw0 5 1 (by norm_num)
  have g1 := one_agree (agreeAll_right hA1) e1
  rw [e45] at hA2
  have g4 := agree_of_mem hA2 (List.mem_cons_self ..)
  have g5 := agree_of_mem hA2 (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  have g6 := one_agree hB1 e6
  constructor
  · rw [relSeg_add 35 2 4, relSeg_add 37 2 2]
    refine agreeAll_app (agreeAll_left hA) (agreeAll_app ?_ (agreeAll_right hA))
    rw [relSeg_cw0 1 2 (by norm_num)]
    exact cw0_wordLin hpow hpw hrest g1 g4 g5 g6 (by decide)
  · rw [relSeg_add 41 1 5, relSeg_add 42 2 3]
    refine agreeAll_app hB1 (agreeAll_app ?_ (agreeAll_right hB))
    rw [relSeg_cw0 6 2 (by norm_num)]
    exact cw0_wordLin hpow hpw hrest g1 g4 g5 g6 (by decide)

end CertificateChecks.KernelKDenseP.MonFive

end
