module

public import Certificates.Kernel.HS589206.KChk
public import Certificates.Kernel.HS589207.Final

set_option maxRecDepth 100000

public section

namespace CFSG.KD.HS589206.Facts

open CFSG.KC.DcHSOutK CFSG.KC.E64F CFSG.KC.Enum CFSG.Quasithin.H13.LocDbl.HSLoc
  CFSG.Quasithin.H13.LocDbl.DcNative CFSG.Quasithin.H13.LocDbl.DcRank
  CFSG.KD.HS589207 CFSG.KD.HS589207.Tabs CFSG.KD.HS589207.Trees CFSG.KD.HS589206.KChk

theorem cntBlk_add (b : Nat) (f : Nat → Bool) (m : Nat) :
    ∀ n, cntBlk b f (m + n) = cntBlk b f m + cntBlk (b + m) f n
  | 0 => rfl
  | n + 1 => by
    have e1 : cntBlk b f (m + (n + 1)) = cntBlk b f (m + n) + cond (f (b + (m + n))) 1 0 := rfl
    have e2 : cntBlk (b + m) f (n + 1) = cntBlk (b + m) f n + cond (f (b + m + n)) 1 0 := rfl
    rw [e1, e2, cntBlk_add b f m n, Nat.add_assoc b m n, Nat.add_assoc]

theorem cntBlk_filter (f : Nat → Bool) : ∀ n, ((List.range n).filter f).length = cntBlk 0 f n
  | 0 => rfl
  | n + 1 => by
    have e : cntBlk 0 f (n + 1) = cntBlk 0 f n + cond (f (0 + n)) 1 0 := rfl
    rw [e, List.range_succ, List.filter_append, List.length_append, cntBlk_filter f n,
      Nat.zero_add]
    cases h : f n <;> simp [h]

theorem anyBlk_spec {b : Nat} {f : Nat → Bool} :
    ∀ {len : Nat}, anyBlk b f len = true → ∃ i < len, f (b + i) = true
  | 0, h => by
    have e : anyBlk b f 0 = false := rfl
    rw [e] at h
    exact absurd h Bool.false_ne_true
  | len + 1, h => by
    have e : anyBlk b f (len + 1) = (f (b + len) || anyBlk b f len) := rfl
    rw [e, Bool.or_eq_true] at h
    rcases h with h | h
    · exact ⟨len, by omega, h⟩
    · obtain ⟨i, hi, hf⟩ := anyBlk_spec h
      exact ⟨i, by omega, hf⟩

theorem anyM_spec {f : Nat → Bool} (h : anyM f = true) : ∃ k < 11520, f k = true := by
  unfold anyM at h
  simp only [Bool.or_eq_true] at h
  rcases h with ((h | h) | h) | h
  · obtain ⟨i, hi, hf⟩ := anyBlk_spec h
    exact ⟨0 + i, by omega, hf⟩
  · obtain ⟨i, hi, hf⟩ := anyBlk_spec h
    exact ⟨2880 + i, by omega, hf⟩
  · obtain ⟨i, hi, hf⟩ := anyBlk_spec h
    exact ⟨5760 + i, by omega, hf⟩
  · obtain ⟨i, hi, hf⟩ := anyBlk_spec h
    exact ⟨8640 + i, by omega, hf⟩

theorem pairwise_of_incB : ∀ {l : List Nat}, incB l = true → l.Pairwise (· < ·)
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: l, h => by
    have e : incB (a :: b :: l) = (Nat.blt a b && incB (b :: l)) := rfl
    rw [e, Bool.and_eq_true, Nat.blt_eq] at h
    have hp := pairwise_of_incB h.2
    refine List.Pairwise.cons (fun x hx => ?_) hp
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h.1
    · exact Nat.lt_trans h.1 (List.rel_of_pairwise_cons hp hx)

theorem eq_of_pairwise_mem : ∀ {l m : List Nat}, l.Pairwise (· < ·) → m.Pairwise (· < ·) →
    (∀ x, x ∈ l ↔ x ∈ m) → l = m
  | [], [], _, _, _ => rfl
  | [], b :: _, _, _, h => absurd ((h b).2 List.mem_cons_self) (List.not_mem_nil)
  | a :: _, [], _, _, h => absurd ((h a).1 List.mem_cons_self) (List.not_mem_nil)
  | a :: l, b :: m, hl, hm, h => by
    have ha := (h a).1 List.mem_cons_self
    have hb := (h b).2 List.mem_cons_self
    have hab : a = b := by
      rcases List.mem_cons.1 ha with e | e
      · exact e
      rcases List.mem_cons.1 hb with e' | e'
      · exact e'.symm
      have := List.rel_of_pairwise_cons hm e
      have := List.rel_of_pairwise_cons hl e'
      omega
    subst hab
    congr 1
    refine eq_of_pairwise_mem hl.of_cons hm.of_cons fun x => ⟨fun hx => ?_, fun hx => ?_⟩
    · have hlt := List.rel_of_pairwise_cons hl hx
      rcases List.mem_cons.1 ((h x).1 (List.mem_cons_of_mem _ hx)) with e | e
      · omega
      · exact e
    · have hlt := List.rel_of_pairwise_cons hm hx
      rcases List.mem_cons.1 ((h x).2 (List.mem_cons_of_mem _ hx)) with e | e
      · omega
      · exact e

theorem F0_lt : ∀ f ∈ F0, f < 100 := by decide

theorem good_k {i : Nat} (hi : i < 2) : Good 100 (kTabs.getD i #[]) (K i) := by
  have e : kTabs.getD i #[] = tabW 100 AB (kWords.getD i []) := by
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl
  rw [e]
  refine CFSG.KC.DcK.good_tabW fun l hl => good_AB l ?_
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> revert l <;> decide

theorem kTabs_size : kTabs.size = 2 := by simp [kTabs, tabsOf, kWords]

theorem mTabs_size : mTabs.size = 2 := rfl

theorem array_all {a : Array (Array Nat)} {p : Array Nat → Bool}
    (h : ∀ i < a.size, p (a.getD i #[]) = true) : a.all p = true := by
  rw [Array.all_eq_true]
  intro i hi
  have e : a[i] = a.getD i #[] := by simp [Array.getD_eq_getD_getElem?, hi]
  rw [e]
  exact h i hi

theorem kfix' : ∀ i < 2, (∀ q < 100, K i q < 100) ∧ K i 0 = 0 ∧ K i 1 = 1 := by
  have h := KChk.kfix
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  unfold fix01 at h3 h4
  rw [Bool.and_eq_true] at h3 h4
  intro i hi
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
  · exact ⟨ltF_spec h1, Nat.eq_of_beq_eq_true h3.1, Nat.eq_of_beq_eq_true h3.2⟩
  · exact ⟨ltF_spec h2, Nat.eq_of_beq_eq_true h4.1, Nat.eq_of_beq_eq_true h4.2⟩

open CFSG.KD.HS589207.Final in
theorem cent_ok : centOK = true := by
  unfold centOK
  rw [mElems_toList, List.all_map, List.all_eq_true]
  intro m hm
  have hm' := List.mem_range.1 hm
  have e := CFSG.KS.allN_spec (Scans.slices KChk.c0 KChk.c1 KChk.c2 KChk.c3) m hm'
  have g : (!(commT (tab m) (kTabs.getD 0 #[]) && commT (tab m) (kTabs.getD 1 #[])) ||
      tab m == idT 100) = centT m := by
    unfold centT
    rw [commT_eq (good_mElems m hm') (good_k (by norm_num)),
      commT_eq (good_mElems m hm') (good_k (by norm_num)), beq_eq (good_mElems m hm') good_idT]
  exact g.trans e

open CFSG.KD.HS589207.Final in
theorem cent_w_ok : centWOK = true := by
  unfold centWOK
  rw [mElems_toList, List.all_map, List.all_eq_true]
  intro m hm
  have hm' := List.mem_range.1 hm
  have e := CFSG.KS.allN_spec (Scans.slices KChk.w0 KChk.w1 KChk.w2 KChk.w3) m hm'
  have hw := good_compT good_wTab (good_mElems m hm')
  have g : (!(commT (compT wTab (tab m)) (kTabs.getD 0 #[]) &&
      commT (compT wTab (tab m)) (kTabs.getD 1 #[]))) = centWT m := by
    unfold centWT
    rw [commT_eq hw (good_k (by norm_num)), commT_eq hw (good_k (by norm_num))]
  exact g.trans e

open CFSG.KD.HS589207.Final in
theorem k_count : kCount = true := by
  unfold kCount
  rw [decide_eq_true_iff, mElems_toList, List.filter_map, List.length_map]
  have e : ((fun t => img t 0 == 0 && img t 1 == 1) ∘ tab) = fun k =>
      if k < 11520 then fix01 (mF k) else ((fun t => img t 0 == 0 && img t 1 == 1) ∘ tab) k := by
    funext k
    split
    · rename_i hk
      simp only [Function.comp, fix01]
      rw [good_img (good_mElems k hk) (by norm_num : 0 < 100),
        good_img (good_mElems k hk) (by norm_num : 1 < 100), nbeq, nbeq]
    · rfl
  have e2 : (List.range 11520).filter ((fun t => img t 0 == 0 && img t 1 == 1) ∘ tab) =
      (List.range 11520).filter fun k => fix01 (mF k) := by
    apply List.filter_congr
    intro k hk
    rw [e]
    simp [List.mem_range.1 hk]
  rw [e2, cntBlk_filter]
  have s : cntBlk 0 (fun k => fix01 (mF k)) 11520 =
      cntBlk 0 (fun k => fix01 (mF k)) 2880 + cntBlk 2880 (fun k => fix01 (mF k)) 2880 +
        cntBlk 5760 (fun k => fix01 (mF k)) 2880 + cntBlk 8640 (fun k => fix01 (mF k)) 2880 := by
    rw [cntBlk_add 0 _ 8640 2880, cntBlk_add 0 _ 5760 2880, cntBlk_add 0 _ 2880 2880]
  rw [s]
  exact Nat.le_of_ble_eq_true KChk.kcount

open CFSG.KD.HS589207.Final in
theorem k_in_m : kInM = true := by
  unfold kInM
  apply array_all
  intro i hi
  rw [kTabs_size] at hi
  have hk := good_k hi
  obtain ⟨-, h0, h1⟩ := kfix' i hi
  rw [good_img hk (by norm_num : 0 < 100), good_img hk (by norm_num : 1 < 100), h0, h1]
  simp only [beq_self_eq_true, Bool.true_and]
  have hm := KChk.kmem
  rw [Bool.and_eq_true] at hm
  obtain ⟨k, hk', he⟩ : ∃ k < 11520, eqF (mF k) (K i) = true := by
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
    · exact anyM_spec hm.1
    · exact anyM_spec hm.2
  rw [arr_contains_iff, mElems_toList, List.mem_map]
  exact ⟨k, List.mem_range.2 hk', good_ext (good_mElems k hk') hk (eqF_spec he)⟩

theorem m_pres : mPres = true := by
  unfold mPres
  apply array_all
  intro t ht
  rw [mTabs_size] at ht
  have hg := good_mTabs t (by rw [mTabs_size]; exact ht)
  have h := CFSG.KS.allN_spec KChk.pres t ht
  simp only [Bool.and_eq_true] at h ⊢
  refine ⟨?_, ?_⟩
  · have e := h.1
    unfold inF0 at e
    rw [List.all_map, List.all_eq_true] at e
    rw [List.all_eq_true]
    intro f hf
    rw [good_img hg (F0_lt f hf)]
    exact e f hf
  · rw [good_img hg (by norm_num : 0 < 100), good_img hg (by norm_num : 1 < 100), nbeq, nbeq,
      nbeq, nbeq]
    exact h.2

theorem orbRows_getD {N k : Nat} (PA : List (Array Nat)) (hk : k < N) :
    (orbRows N PA).getD k [] = maskOf (PA.map fun A => A.getD k 0) := by
  unfold orbRows
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk, Option.map_some,
    Option.getD_some]

theorem orbRows_length (N : Nat) (PA : List (Array Nat)) : (orbRows N PA).length = N := by
  simp [orbRows]

theorem orbF_getD {k : Nat} (hk : k < 3850) :
    orbF.getD k [] = maskOf (F0.map (ePath FP FL A 3850 k)) := by
  unfold orbF
  rw [orbRows_getD _ hk, List.map_map]
  apply congrArg maskOf
  apply List.map_congr_left
  intro f hf
  rw [Function.comp_apply, treeF_eq]
  change (ptsArr AB ((List.range 3850).map FP).toArray ((List.range 3850).map FL).toArray 3850
    f).getD k 0 = _
  refine ptsArr_spec f (fun t ht => good_AB t (by rw [AB_size] at ht; exact ht)) (ePath_zero _ f)
    (fun k hk0 hk => ?_)
    (fun k hk => ePath_lt (fun l hl q hq => A_lt hl hq) FL_lt FP_lt 3850 k hk f (F0_lt f hf)) k hk
  rw [getD_toArray_map _ hk, getD_toArray_map _ hk]
  exact ⟨FP_lt k hk0 hk, by rw [AB_size]; exact FL_lt k hk0 hk, ePath_step FP_lt (by omega) hk f⟩

theorem orbF_eq : orbF = (List.range 3850).map fun k => maskOf (F0.map (ePath FP FL A 3850 k)) := by
  apply List.ext_getElem
  · unfold orbF
    rw [orbRows_length, List.length_map, List.length_range]
  · intro n h1 h2
    have hn : n < 3850 := by simpa using h2
    have e := orbF_getD hn
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, Option.getD_some] at e
    rw [e, List.getElem_map, List.getElem_range]

theorem mem_setT : ∀ k < 3850, ∀ x, x ∈ setT FR.TF k ↔ x ∈ F0.map (ePath FP FL A 3850 k) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk x
    by_cases h0 : k = 0
    · subst h0
      have e : F0.map (ePath FP FL A 3850 0) = F0.map id :=
        List.map_congr_left fun q _ => ePath_zero _ q
      rw [fent'.2, e, List.map_id]
    · obtain ⟨hp, hl, ht⟩ := frec.tree k (by omega) hk
      rw [ht, stFn, List.mem_mergeSort, List.mem_map, List.mem_map]
      constructor
      · rintro ⟨y, hy, rfl⟩
        obtain ⟨z, hz, rfl⟩ := List.mem_map.1 ((ih _ hp (by omega) y).1 hy)
        refine ⟨z, hz, ?_⟩
        rw [ePath_step FP_lt h0 hk, good_img (good_AB _ hl)
          (ePath_lt (fun l hl q hq => A_lt hl hq) FL_lt FP_lt 3850 _ (by omega) z (F0_lt z hz))]
      · rintro ⟨z, hz, rfl⟩
        refine ⟨ePath FP FL A 3850 (FP k) z,
          (ih _ hp (by omega) _).2 (List.mem_map.2 ⟨z, hz, rfl⟩), ?_⟩
        rw [ePath_step FP_lt h0 hk, good_img (good_AB _ hl)
          (ePath_lt (fun l hl q hq => A_lt hl hq) FL_lt FP_lt 3850 _ (by omega) z (F0_lt z hz))]

theorem maskOf_mem {l m : List Nat} (hl : ∀ x ∈ l, x < 100) (hm : ∀ x ∈ m, x < 100)
    (h : maskOf l = maskOf m) : ∀ x, x ∈ l ↔ x ∈ m := by
  intro x
  by_cases hx : x < 100
  · have e := congrArg (fun r => r.getD x false) h
    simp only [maskOf, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hx,
      Option.map_some, Option.getD_some] at e
    rw [← List.contains_iff_mem, ← List.contains_iff_mem, e]
  · exact ⟨fun h' => absurd (hl x h') hx, fun h' => absurd (hm x h') hx⟩

theorem setT_lt {k : Nat} (hk : k < 3850) : ∀ x ∈ F0.map (ePath FP FL A 3850 k), x < 100 := by
  intro x hx
  obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hx
  exact ePath_lt (fun l hl q hq => A_lt hl hq) FL_lt FP_lt 3850 k hk z (F0_lt z hz)

theorem tree_ok : treeOK = true := by
  unfold treeOK
  rw [Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · unfold enumOK
    rw [treeF_eq]
    simp only [List.all_eq_true]
    intro k hk
    have hk' := List.mem_range.1 hk
    simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq]
    by_cases h0 : k = 0
    · exact Or.inl h0
    · right
      rw [getD_toArray_map _ hk', getD_toArray_map _ hk', AB_size]
      exact ⟨FP_lt k (by omega) hk', FL_lt k (by omega) hk'⟩
  · rw [decide_eq_true_iff, orbF_eq]
    refine List.Nodup.map_on (fun a ha b hb h => ?_) List.nodup_range
    have ha' := List.mem_range.1 ha
    have hb' := List.mem_range.1 hb
    have hm := maskOf_mem (setT_lt ha') (setT_lt hb') h
    have e : setT FR.TF a = setT FR.TF b :=
      eq_of_pairwise_mem (pairwise_of_incB (CFSG.KS.allN_spec KChk.fsort a ha'))
        (pairwise_of_incB (CFSG.KS.allN_spec KChk.fsort b hb'))
        fun x => by rw [mem_setT a ha' x, mem_setT b hb' x]; exact hm x
    exact frec.inj a ha' b hb' (by rw [e])

theorem k_u_ok : kUOK = true := by
  have h := KChk.uinv
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  have hu : Good 100 (invT uTab) KChk.uI := good_invT good_uTab (ltF_spec h1) (eqF_spec h3)
    (eqF_spec h2)
  have hkU : kU < 3850 := by decide
  unfold kUOK
  rw [orbF_getD hkU, beq_iff_eq]
  have e1 : F0.map (ePath FP FL A 3850 kU) = F0.map gF :=
    List.map_congr_left fun f hf => CFSG.KD.HS589207.Final.good_map_eq
      (good_treeElems kU hkU) good_g f (F0_lt f hf)
  have e2 : F0.map (img (invT uTab)) = F0.map KChk.uI :=
    List.map_congr_left fun f hf => good_img hu (F0_lt f hf)
  rw [e1, e2]
  unfold maskOf
  apply List.map_congr_left
  intro x hx
  exact beq_iff_eq.1 (List.all_eq_true.1 h4 x hx)

end CFSG.KD.HS589206.Facts

end
