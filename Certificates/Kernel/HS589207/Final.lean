module

public import Certificates.Kernel.HS589207.Trees
public import Certificates.Kernel.HS589207.E0
public import Certificates.Kernel.HS589207.Scans

set_option maxRecDepth 100000

public section

namespace CFSG.KD.HS589207.Final

open CFSG.KC.DcHSOutK CFSG.KC.E64F CFSG.KC.Enum CFSG.Quasithin.H13.LocDbl.HSLoc
  CFSG.Quasithin.H13.LocDbl.DcNative CFSG.Quasithin.H13.LocDbl.DcRank
  CFSG.KD.HS589207.Tabs CFSG.KD.HS589207.Trees

theorem contains_iff {l : List Nat} {a : Nat} : l.contains a = true ↔ a ∈ l := by simp

theorem arr_contains_iff {l : List (Array Nat)} {a : Array Nat} :
    l.contains a = true ↔ a ∈ l := by simp

theorem toList_eq {a : Array (Array Nat)} {N : Nat} (h : a.size = N) :
    a.toList = (List.range N).map fun k => a.getD k #[] := by
  apply List.ext_getElem
  · simp [h]
  · intro n h1 h2
    have hn : n < a.size := by simpa using h1
    rw [List.getElem_map, List.getElem_range, Array.getElem_toList, Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_getElem hn, Option.getD_some]

theorem filter_len {N : Nat} {p : Nat → Bool} {I : List Nat} (hI : I.Nodup)
    (hlt : ∀ k ∈ I, k < N) (hp : ∀ k < N, p k = I.contains k) :
    ((List.range N).filter p).length = I.length := by
  apply List.Perm.length_eq
  apply (List.perm_ext_iff_of_nodup (List.Nodup.filter _ List.nodup_range) hI).2
  intro k
  simp only [List.mem_filter, List.mem_range]
  constructor
  · rintro ⟨hk, hpk⟩
    rw [hp k hk] at hpk
    exact contains_iff.1 hpk
  · intro hk
    exact ⟨hlt k hk, by rw [hp k (hlt k hk)]; exact contains_iff.2 hk⟩

theorem all_mem_congr {l m : List Nat} {f : Nat → Bool} (h : ∀ x, x ∈ l ↔ x ∈ m) :
    l.all f = m.all f := by
  apply Bool.eq_iff_iff.2
  simp only [List.all_eq_true]
  exact ⟨fun H x hx => H x ((h x).2 hx), fun H x hx => H x ((h x).1 hx)⟩

abbrev tab (k : Nat) : Array Nat := mElems.getD k #[]

theorem mElems_toList : mElems.toList = (List.range 11520).map tab := toList_eq mElems_size

theorem idx' : I0.Nodup ∧ (∀ k ∈ I0, k < 11520) ∧ IO.Nodup ∧ (∀ k ∈ IO, k < 11520) := by
  have h := E0.idx
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨a, b⟩, c⟩, d⟩ := h
  exact ⟨a, fun k hk => by simpa [Nat.blt_eq] using b k hk, c,
    fun k hk => by simpa [Nat.blt_eq] using d k hk⟩

@[expose] noncomputable def I0f : List Nat := (List.range 11520).filter fun k => I0.contains k

theorem mem_I0f {k : Nat} : k ∈ I0f ↔ k ∈ I0 := by
  simp only [I0f, List.mem_filter, List.mem_range, contains_iff]
  exact ⟨fun h => h.2, fun h => ⟨idx'.2.1 k h, h⟩⟩

theorem e0_eq : e0Elems = I0f.map tab := by
  unfold e0Elems I0f
  rw [mElems_toList, List.filter_map]
  congr 1
  apply List.filter_congr
  intro k hk
  have hk' := List.mem_range.1 hk
  simp only [Function.comp]
  rw [fix_eq (good_mElems k hk')]
  have := CFSG.KS.allN_spec E0.fix k hk'
  exact beq_iff_eq.1 this

theorem tab_good {k : Nat} (hk : k ∈ I0f) : Good 100 (tab k) (mF k) :=
  good_mElems k (List.mem_range.1 (List.mem_filter.1 hk).1)

theorem e0_all {t : Array Nat} {f : Nat → Nat} (ht : Good 100 t f) (g : Nat → Nat → Nat)
    (hg : ∀ k ∈ I0f, ∀ s, Good 100 s (mF k) → commT t s = commF f (g k)) :
    e0Elems.all (commT t) = I0.all fun j => commF f (g j) := by
  rw [e0_eq, List.all_map]
  rw [show I0.all (fun j => commF f (g j)) = I0f.all (fun j => commF f (g j)) from
    all_mem_congr fun x => mem_I0f.symm]
  apply all_congr'
  intro k hk
  exact hg k hk _ (tab_good hk)

theorem e0_ok : e0OK = true := by
  unfold e0OK
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [e0_eq, List.length_map, I0f, filter_len idx'.1 idx'.2.1 fun k _ => rfl]
    simp [I0]
  · unfold cent0List
    rw [mElems_toList, List.filter_map, List.all_map, List.all_eq_true]
    intro m hm
    rw [List.mem_filter] at hm
    obtain ⟨hmr, hp⟩ := hm
    have hm' := List.mem_range.1 hmr
    simp only [Function.comp] at hp ⊢
    rw [e0_all (good_mElems m hm') mF (fun k _ s hs => commT_eq (good_mElems m hm') hs)] at hp
    have hc := CFSG.KS.allN_spec Scans.cent m hm'
    rw [hp, Bool.not_true, Bool.false_or] at hc
    rw [e0_eq, arr_contains_iff]
    exact List.mem_map.2 ⟨m, mem_I0f.2 (contains_iff.1 hc), rfl⟩
  · unfold outList
    rw [mElems_toList, List.filter_map]
    simp only [List.length_map]
    have e : (List.filter ((fun m => e0Elems.all (commT (compT wTab m))) ∘ tab)
        (List.range 11520)).length = IO.length := by
      apply filter_len idx'.2.2.1 idx'.2.2.2
      intro m hm
      simp only [Function.comp]
      have hw := good_compT good_wTab (good_mElems m hm)
      rw [e0_all hw mF (fun k _ s hs => commT_eq hw hs)]
      exact beq_iff_eq.1 (CFSG.KS.allN_spec Scans.out m hm)
    rw [e]
    simp [IO]

@[expose] def gL (p : Nat) : Array Nat :=
  conjT (mElems.getD (goodIdx.getD p 0) #[]) (invT (mElems.getD (goodIdx.getD p 0) #[])) r0Tab

theorem goodList_eq : goodList = (List.range 10).map gL := by
  have e : goodIdx = (List.range 10).map fun p => goodIdx.getD p 0 := by decide
  unfold goodList
  conv_lhs => rw [e]
  rw [List.map_map]
  rfl

theorem good_gL {p : Nat} (hp : p < 10) : Good 100 (gL p) (cF p) := by
  have hj : goodIdx.getD p 0 < 11520 := by
    revert p
    decide
  have h := CFSG.KS.allN_spec Gen.goodInv p hp
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have hg := good_mElems _ hj
  exact good_conjT hg (good_invT hg (ltF_spec h1) (eqF_spec h3) (eqF_spec h2)) good_r0Tab

theorem good_ok : goodOK = true := by
  unfold goodOK
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [mElems_size]
    decide
  · intro j hj
    rw [mElems_size]
    revert j
    decide
  · decide
  · rw [goodList_eq]
    apply pwDistinct_of_pairwise
    rw [List.pairwise_map]
    refine List.pairwise_lt_range.imp_of_mem fun {a b} ha hb hab e => ?_
    have ha' := List.mem_range.1 ha
    have hb' := List.mem_range.1 hb
    have hd := CFSG.KS.allN_spec (CFSG.KS.allN_spec Gen.goodDist a ha') b hb'
    have hab' : Nat.blt a b = true := by simpa [Nat.blt_eq] using hab
    rw [hab', Bool.not_true, Bool.false_or] at hd
    have := beq_eq (good_gL ha') (good_gL hb')
    rw [e, beq_self_eq_true] at this
    rw [← this] at hd
    exact absurd hd (by decide)
  · rw [goodList_eq]
    intro t ht
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ht
    have hp' := List.mem_range.1 hp
    have h := CFSG.KS.allN_spec Gen.goodOut p hp'
    simp only [Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    have hIO := contains_iff.1 h1
    have hm := idx'.2.2.2 _ hIO
    unfold outList
    rw [mElems_toList, List.filter_map, arr_contains_iff, List.mem_map]
    refine ⟨tab (IG.getD p 0), List.mem_map.2 ⟨IG.getD p 0, List.mem_filter.2
      ⟨List.mem_range.2 hm, ?_⟩, rfl⟩, ?_⟩
    · simp only [Function.comp]
      have hw := good_compT good_wTab (good_mElems _ hm)
      rw [e0_all hw mF (fun k _ s hs => commT_eq hw hs)]
      have := CFSG.KS.allN_spec Scans.out _ hm
      rw [beq_iff_eq.1 this]
      exact h1
    · exact good_ext (good_compT good_wTab (good_mElems _ hm)) (good_gL hp') (eqF_spec h2)

theorem moore_letters : ∀ w ∈ mooreWords, ∀ l ∈ w, l < 4 := by decide

theorem good_moore {w : List Nat} (hw : w ∈ mooreWords) :
    Good 100 (tabW 100 AB w) (wordF A w) :=
  CFSG.KC.DcK.good_tabW fun l hl => good_AB l (moore_letters w hw l hl)

theorem good_mooreX {i : Nat} (h1 : 1 ≤ i) (h6 : i ≤ 6) : Good 100 (mooreX i) (mx i) := by
  have hn : i - 1 < mooreWords.length := by simp [mooreWords]; omega
  have e : mooreX i = tabW 100 AB (mooreWords.getD (i - 1) []) := by
    simp only [mooreX, mooreTabs, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem hn, Option.map_some, Option.getD_some]
  have hw : mooreWords.getD (i - 1) [] ∈ mooreWords := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn, Option.getD_some]
    exact List.getElem_mem hn
  rw [e]
  exact good_moore hw

theorem moore_eq : mooreOK = mooreK := by
  have g1 := good_mooreX (i := 1) (by norm_num) (by norm_num)
  have p1 : (compT (mooreX 1) (compT (mooreX 1) (mooreX 1)) == idT 100) =
      eqF (fun q => mx 1 (mx 1 (mx 1 q))) (fun q => q) :=
    beq_eq (good_compT g1 (good_compT g1 g1)) good_idT
  have p2 : (mooreX 1 != idT 100) = !eqF (mx 1) (fun q => q) := by
    rw [bne, beq_eq g1 good_idT]
  have p3 : (List.range' 2 5).all (fun j => (compT (mooreX j) (mooreX j) == idT 100) &&
      (let h := compT (mooreX (j - 1)) (mooreX j); compT h (compT h h) == idT 100)) =
      (List.range' 2 5).all (fun j => eqF (fun q => mx j (mx j q)) (fun q => q) &&
      eqF (fun q => mx (j - 1) (mx j (mx (j - 1) (mx j (mx (j - 1) (mx j q)))))) (fun q => q)) := by
    apply all_congr'
    intro j hj
    rw [List.mem_range'_1] at hj
    have gj := good_mooreX (i := j) (by omega) (by omega)
    have gj1 := good_mooreX (i := j - 1) (by omega) (by omega)
    have gh := good_compT gj1 gj
    simp only []
    rw [beq_eq (good_compT gj gj) good_idT, beq_eq (good_compT gh (good_compT gh gh)) good_idT]
  have p4 : (List.range' 1 4).all (fun i => (List.range' (i + 2) (5 - i)).all fun j =>
      let h := compT (mooreX i) (mooreX j); compT h h == idT 100) =
      (List.range' 1 4).all (fun i => (List.range' (i + 2) (5 - i)).all fun j =>
      eqF (fun q => mx i (mx j (mx i (mx j q)))) (fun q => q)) := by
    apply all_congr'
    intro i hi
    rw [List.mem_range'_1] at hi
    apply all_congr'
    intro j hj
    rw [List.mem_range'_1] at hj
    have gi := good_mooreX (i := i) (by omega) (by omega)
    have gj := good_mooreX (i := j) (by omega) (by omega)
    have gh := good_compT gi gj
    simp only []
    rw [beq_eq (good_compT gh gh) good_idT]
  have p5 : mooreTabs.all (fun t => commT t r0Tab) =
      mooreWords.all (fun w => commF (wordF A w) r0F) := by
    unfold mooreTabs
    rw [List.all_map]
    apply all_congr'
    intro w hw
    exact commT_eq (good_moore hw) good_r0Tab
  unfold mooreOK mooreK
  rw [p1, p2, p3, p4, p5]

theorem moore_ok : mooreOK = true := by rw [moore_eq]; exact Gen.moore

theorem cjElems_good : ∀ k < 1100, Good 100 (cjElems.getD k #[]) (ePath CP CL A 1100 k) := by
  unfold cjElems
  rw [cjTree_eq]
  refine enumTabs_good good_AB (fun q _ => ePath_zero _ q) (fun k hk0 hk => ?_)
    (fun k hk q hq => ePath_lt (fun l hl q hq => A_lt hl hq) CL_lt CP_lt 1100 k hk q hq)
  rw [getD_toArray_map _ hk, getD_toArray_map _ hk]
  exact ⟨CP_lt k hk0 hk, CL_lt k hk0 hk, fun q _ => ePath_step CP_lt (by omega) hk q⟩

theorem good_map_eq {t : Array Nat} {f g : Nat → Nat} (hf : Good 100 t f) (hg : Good 100 t g) :
    ∀ p < 100, f p = g p := fun p hp => by rw [← (hf.2 p hp).1, ← (hg.2 p hp).1]

theorem conj_map : ∀ k < 1100, ∀ q < 100,
    ePath CP CL A 1100 k (r0F (ePathI CP CL A 1100 k q)) = fl (CR.TF k) q := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk q hq
    by_cases h0 : k = 0
    · subst h0
      rw [ePath_zero, ePathI_zero]
      exact (cent'.2 q hq).symm
    · have hp := CP_lt k (by omega) hk
      have hl := CL_lt k (by omega) hk
      have e := TC_step (by omega) hk
      have hs : Good 100 (stCn (CL k) (TC (CP k)))
          (fun q => A (CL k) (fl (CR.TF (CP k)) (A (CFSG.KC.DcHSOutK.invL (CL k)) q))) := by
        unfold stCn
        rw [invL_eq]
        exact good_conjT (good_AB _ hl) (good_AB _ (invL_lt hl)) (good_TC (by omega))
      rw [← e] at hs
      rw [good_map_eq (good_TC hk) hs q hq, ePathI_step CP_lt h0 hk, ePath_step CP_lt h0 hk,
        ih (CP k) hp (by omega) _ (A_lt (invL_lt hl) hq)]

theorem cjConj_eq {k : Nat} (hk : k < 1100) :
    conjT (cjElems.getD k #[]) (invT (cjElems.getD k #[])) r0Tab = TC k := by
  have hA : ∀ l < 4, ∀ q < 100, A l q < 100 := fun l hl q hq => A_lt hl hq
  have hinv := ePath_inv hA (fun l hl q hq => A_inv hl hq) CL_lt CP_lt
  have hg := cjElems_good k hk
  have hi := good_invT hg (fun p hp => ePathI_lt hA CL_lt CP_lt 1100 k hk p hp)
    (fun p hp => (hinv k hk p hp).1) (fun p hp => (hinv k hk p hp).2)
  exact good_ext (good_conjT hg hi good_r0Tab) (good_TC hk) fun q hq => conj_map k hk q hq

theorem cjElems_size : cjElems.size = 1100 := by
  unfold cjElems
  rw [cjTree_eq]
  simp [enumTabs]

theorem cj_ok : cjOK = true := by
  unfold cjOK
  rw [Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · unfold enumOK
    rw [cjTree_eq]
    simp only [List.all_eq_true]
    intro k hk
    have hk' := List.mem_range.1 hk
    simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq]
    by_cases h0 : k = 0
    · exact Or.inl h0
    · right
      rw [getD_toArray_map _ hk', getD_toArray_map _ hk', AB_size]
      exact ⟨CP_lt k (by omega) hk', CL_lt k (by omega) hk'⟩
  · have e : cjConjs = (List.range 1100).map TC := by
      unfold cjConjs
      rw [toList_eq cjElems_size, List.map_map]
      apply List.map_congr_left
      intro k hk
      exact cjConj_eq (List.mem_range.1 hk)
    rw [e]
    apply pwDistinct_of_pairwise
    rw [List.pairwise_map]
    exact List.pairwise_lt_range.imp_of_mem fun {a b} ha hb hab h =>
      absurd (TC_inj (List.mem_range.1 ha) (List.mem_range.1 hb) h) (by omega)

end CFSG.KD.HS589207.Final

end
