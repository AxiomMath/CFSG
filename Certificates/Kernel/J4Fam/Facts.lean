module

public import Certificates.Kernel.J4Fam.Invs
public import Certificates.Kernel.J4Fam.Rows
public import Certificates.Kernel.J4Fam.Fix
public import Certificates.Kernel.J4Fam.Levels
public import Certificates.Kernel.J4Fam.Close
public import Certificates.Kernel.J4Fam.Bounds
public import CFSG.Certificates.Kernel.J4FamSound

public section

namespace CertificateChecks.KernelJ4Fam

open CFSG.KC.J4Fam CFSG.Sporadic.J4.QT CFSG.EvenSporadicStandard.J4Std.DataLocal

attribute [local irreducible] INV CML PTL PTP FB FLL PP TT WALL PL LV0 LV1 LV2 LV3 LV4 LV5 LV6 LV7
  TG0 TG1 TG2 TG3 TG4 TG5 TG6 LVT0 LVT1 LVT2 LVT3 LVT4 LVT5 LVT6 LVT7 FBT FLLT TGT0 TGT1 TGT2 TGT3
  TGT4 TGT5 TGT6 tabL

theorem invs_eq : invs = INV := beq_iff_eq.mp invs_ok

theorem INV_spec : INV.length = 191 ∧ idT ∉ INV ∧ INV.Nodup ∧ ∀ j < 191, WT (INV.getD j []) :=
  invsOK_spec invsOK_ok

theorem nInv_eq : nInv = 191 := by
  unfold nInv
  rw [invs_eq]
  exact INV_spec.1

theorem inv_eq (i : Nat) : inv i = INV.getD i [] := by
  unfold inv
  rw [invs_eq]

theorem commutes_eq (i j : Nat) : commutes i j = comT (INV.getD i []) (INV.getD j []) := by
  unfold commutes comT
  rw [inv_eq, inv_eq]

theorem row_spec {i : Nat} (hi : i < 191) :
    CML.getD i 0 = maskOf ((List.range 191).filter fun j => comT (INV.getD i []) (INV.getD j [])) ∧
    (PTL.getD i []).length = 191 ∧ (∀ x ∈ PTL.getD i [], x < 256) ∧
    PTP.getD i 0 = packR (PTL.getD i []) ∧
    ∀ j < 191, (comT (INV.getD i []) (INV.getD j []) = true →
        (i = j → (PTL.getD i []).getD j 0 = 191) ∧
        (i ≠ j → (PTL.getD i []).getD j 0 < 191 ∧
          INV.getD ((PTL.getD i []).getD j 0) [] = compT (INV.getD i []) (INV.getD j []))) ∧
      (comT (INV.getD i []) (INV.getD j []) = false → (PTL.getD i []).getD j 0 = 0) :=
  rowOK_spec INV_spec.2.2.2 pp_ok tt_ok wall_ok hi (rows_ok i hi)

theorem getD_map_range {α : Type} (f : Nat → α) {n i : Nat} (hi : i < n) (d : α) :
    ((List.range n).map f).getD i d = f i := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getElem_range]

theorem commMasks_getD {i : Nat} (hi : i < 191) : commMasks.getD i 0 = CML.getD i 0 := by
  rw [(row_spec hi).1]
  unfold commMasks
  rw [nInv_eq, getD_map_range _ hi]
  congr 1
  apply List.filter_congr
  intro j _
  rw [commutes_eq]

theorem inv_mem_INV {i : Nat} (hi : i < 191) : INV.getD i [] ∈ INV := by
  rw [List.getD_eq_getElem _ _ (by rw [INV_spec.1]; exact hi)]
  exact List.getElem_mem _

theorem comp_self {i : Nat} (hi : i < 191) : compT (INV.getD i []) (INV.getD i []) = idT := by
  have h : INV.getD i [] ∈ invs := by
    rw [invs_eq]
    exact inv_mem_INV hi
  exact (mem_invs.1 h).2.1

theorem prodIdx_eq {i j : Nat} (hi : i < 191) (hj : j < 191) :
    prodIdx i j = (PTL.getD i []).getD j 0 := by
  obtain ⟨-, -, -, -, h5⟩ := row_spec hi
  obtain ⟨hc1, hc0⟩ := h5 j hj
  unfold prodIdx prodTab
  rw [nInv_eq, getD_map_range _ hi, getD_map_range _ hj, commutes_eq, inv_eq, inv_eq, invs_eq]
  cases hc : comT (INV.getD i []) (INV.getD j [])
  · rw [hc0 hc]
    rfl
  · simp only [if_true]
    by_cases hij : i = j
    · subst hij
      rw [(hc1 hc).1 rfl, comp_self hi, List.idxOf_eq_length INV_spec.2.1, INV_spec.1]
    · obtain ⟨hp, hpe⟩ := (hc1 hc).2 hij
      rw [← hpe, List.getD_eq_getElem _ _ (by rw [INV_spec.1]; exact hp),
        List.Nodup.idxOf_getElem INV_spec.2.2.1]

theorem chkTabs_true : chkTabs = true := by
  unfold chkTabs
  rw [nInv_eq]
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true,
    Bool.not_eq_true']
  intro i hi j hj
  obtain ⟨h1, -, -, -, h5⟩ := row_spec hi
  obtain ⟨hc1, hc0⟩ := h5 j hj
  refine ⟨?_, ?_⟩
  · rw [commMasks_getD hi, h1, testBit_maskOf, commutes_eq]
    simp only [List.mem_filter, List.mem_range, hj, true_and, Bool.decide_eq_true]
  · rw [commutes_eq]
    cases hc : comT (INV.getD i []) (INV.getD j [])
    · exact Or.inl (Or.inr rfl)
    · by_cases hij : i = j
      · exact Or.inl (Or.inl (by simp [hij]))
      · obtain ⟨hp, hpe⟩ := (hc1 hc).2 hij
        refine Or.inr ⟨by rw [prodIdx_eq hi hj]; simpa using hp, ?_⟩
        rw [prodIdx_eq hi hj, inv_eq, hpe, inv_eq, inv_eq]

theorem bitIdx_eq (m : Nat) : bitIdx m = bitIdxK m := by
  unfold bitIdx bitIdxK
  rw [nInv_eq, bitsR_eq, List.range_eq_range']

theorem lt_of_mem_bitIdx {m j : Nat} (h : j ∈ bitIdx m) : j < 191 := by
  have := (mem_bitIdx.1 h).1
  rwa [nInv_eq] at this

theorem fieldR_PTP {i j : Nat} (hi : i < 191) (hj : j < 191) :
    fieldR (PTP.getD i 0) j = prodIdx i j := by
  obtain ⟨-, -, h3, h4, -⟩ := row_spec hi
  rw [h4, fieldR_packR h3, prodIdx_eq hi hj]

theorem lens : CML.length = 191 ∧ PTP.length = 191 := by
  have h := lens_ok
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1, h.1.2⟩

theorem extWith_eq (bs : List Nat) (m i r : Nat) (hr : ∀ j ∈ bs, fieldR r j = prodIdx i j) :
    extWith bs m i = bs.foldl (fun a j => a ||| (1 <<< fieldR r j)) (m ||| (1 <<< i)) := by
  have hmap : bs.foldl (fun a j => a ||| (1 <<< fieldR r j)) (m ||| (1 <<< i)) =
      (bs.map (prodIdx i)).foldl (fun a j => a ||| (1 <<< j)) (m ||| (1 <<< i)) := by
    rw [List.foldl_map]
    apply List.foldl_ext
    intro a j hj
    rw [hr j hj]
  rw [hmap]
  unfold extWith maskOf
  apply Nat.eq_of_testBit_eq
  intro k
  rw [List.foldl_cons, Nat.testBit_or, foldl_maskOf_testBit, foldl_maskOf_testBit, Nat.testBit_or,
    Nat.testBit_or, Nat.zero_testBit, Bool.false_or, Bool.or_assoc]

theorem exts_eq (m : Nat) : exts m = extsK CML PTP m := by
  unfold exts extsK
  rw [extsGo_eq m _ CML PTP 0 (by rw [lens.1, lens.2]), lens.1, ← List.range_eq_range']
  unfold cands
  rw [nInv_eq]
  have hfil : ((List.range 191).filter fun i => !m.testBit i && (m &&& commMasks.getD i 0 == m)) =
      ((List.range 191).filter fun i => !m.testBit i && Nat.beq (m &&& CML.getD (i - 0) 0) m) := by
    apply List.filter_congr
    intro i hi
    rw [Nat.sub_zero, commMasks_getD (List.mem_range.1 hi)]
    congr 1
  rw [hfil]
  apply List.map_congr_left
  intro i hi
  have hi' : i < 191 := List.mem_range.1 (List.mem_filter.1 hi).1
  rw [Nat.sub_zero, ← bitIdx_eq]
  exact extWith_eq _ _ _ _ fun j hj => fieldR_PTP hi' (lt_of_mem_bitIdx hj)

@[expose] noncomputable def LVk (k : Nat) : List Nat := [LV0, LV1, LV2, LV3, LV4, LV5, LV6, LV7].getD k []

theorem mem_next {F : List Nat} {m : Nat} : m ∈ next F ↔ ∃ m0 ∈ F, m ∈ exts m0 := by
  have key : ∀ (l : List Nat) (s : Std.HashSet Nat),
      m ∈ l.foldl (fun (s : Std.HashSet Nat) x => s.insert x) s ↔ m ∈ s ∨ m ∈ l := by
    intro l
    induction l with
    | nil => intro s; simp
    | cons y l ih =>
      intro s
      rw [List.foldl_cons, ih, Std.HashSet.mem_insert, List.mem_cons]
      constructor
      · rintro ((h | h) | h)
        · exact Or.inr (Or.inl (beq_iff_eq.mp h).symm)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
      · rintro (h | h | h)
        · exact Or.inl (Or.inr h)
        · exact Or.inl (Or.inl (beq_iff_eq.mpr h.symm))
        · exact Or.inr h
  unfold next dedup
  rw [Std.HashSet.mem_toList, key, List.mem_flatMap]
  simp

theorem LV_lens : LV0.length = 1 ∧ LV1.length = 191 ∧ LV2.length = 2091 ∧ LV3.length = 3643 ∧
    LV4.length = 1449 ∧ LV5.length = 130 ∧ LV6.length = 2 := by
  have h := lens_lv
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  tauto

theorem TG_lens : TG0.length = LV0.length ∧ TG1.length = LV1.length ∧ TG2.length = LV2.length ∧
    TG3.length = LV3.length ∧ TG4.length = LV4.length ∧ TG5.length = LV5.length ∧
    TG6.length = LV6.length := by
  have h := tg_ok
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  tauto

theorem trees : treeOK LVT0 LV0 = true ∧ treeOK LVT1 LV1 = true ∧ treeOK LVT2 LV2 = true ∧
    treeOK LVT3 LV3 = true ∧ treeOK LVT4 LV4 = true ∧ treeOK LVT5 LV5 = true ∧
    treeOK LVT6 LV6 = true ∧ treeOK LVT7 LV7 = true ∧ treeOK FBT FB = true ∧
    treeOK FLLT FLL = true := by
  have h := tr_ok
  simp only [Bool.and_eq_true] at h
  tauto

theorem level_step {k : Nat} (hk : k < 7) (m : Nat) :
    (∃ m0 ∈ LVk k, m ∈ exts m0) ↔ m ∈ LVk (k + 1) := by
  simp only [exts_eq]
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := LV_lens
  obtain ⟨t0, t1, t2, t3, t4, t5, t6⟩ := TG_lens
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, -, -⟩ := trees
  interval_cases k
  · exact levelOK_mem r1 r0 tg_tr0 t0 cv_ok0 (nc := 1) (by rw [h0]; norm_num) cl_ok0 m
  · exact levelOK_mem r2 r1 tg_tr1 t1 cv_ok1 (nc := 2) (by rw [h1]; norm_num) cl_ok1 m
  · exact levelOK_mem r3 r2 tg_tr2 t2 cv_ok2 (nc := 17) (by rw [h2]; norm_num) cl_ok2 m
  · exact levelOK_mem r4 r3 tg_tr3 t3 cv_ok3 (nc := 29) (by rw [h3]; norm_num) cl_ok3 m
  · exact levelOK_mem r5 r4 tg_tr4 t4 cv_ok4 (nc := 12) (by rw [h4]; norm_num) cl_ok4 m
  · exact levelOK_mem r6 r5 tg_tr5 t5 cv_ok5 (nc := 2) (by rw [h5]; norm_num) cl_ok5 m
  · exact levelOK_mem r7 r6 tg_tr6 t6 cv_ok6 (nc := 1) (by rw [h6]; norm_num) cl_ok6 m

theorem mem_lvl : ∀ k < 8, ∀ m, m ∈ lvl k ↔ m ∈ LVk k
  | 0, _, m => by
    rw [lvl_zero]
    change m ∈ [0] ↔ m ∈ LV0
    rw [lv0_ok]
  | k + 1, hk, m => by
    rw [lvl_succ (by omega), mem_next, ← level_step (by omega)]
    constructor
    · rintro ⟨m0, hm0, hm⟩
      exact ⟨m0, (mem_lvl k (by omega) m0).1 hm0, hm⟩
    · rintro ⟨m0, hm0, hm⟩
      exact ⟨m0, (mem_lvl k (by omega) m0).2 hm0, hm⟩

theorem fix_spec {i : Nat} (hi : i < 191) :
    (∀ c < 2048, (FB.getD i 0).testBit c = (actT (INV.getD i []) c == c)) ∧
      FLL.getD i [] = (List.range 2048).filter (FB.getD i 0).testBit :=
  fixRowOK_spec (INV_spec.2.2.2 i hi) pl_ok (fix_ok i hi)

theorem fixLists_getD {i : Nat} (hi : i < 191) : fixLists.getD i [] = FLL.getD i [] := by
  unfold fixLists
  rw [nInv_eq, getD_map_range _ hi, (fix_spec hi).2]
  unfold fixList
  apply List.filter_congr
  intro c hc
  rw [inv_eq, (fix_spec hi).1 c (List.mem_range.1 hc)]

theorem getT_FBT (j : Nat) : getT FBT j 0 = FB.getD j 0 :=
  getT_of_treeOK trees.2.2.2.2.2.2.2.2.1 j 0

theorem getT_FLLT (j : Nat) : getT FLLT j [] = FLL.getD j [] :=
  getT_of_treeOK trees.2.2.2.2.2.2.2.2.2 j []

theorem fixCnt_eq (m : Nat) : fixCnt m = fixCntK FBT FLLT m := by
  unfold fixCnt fixCntK
  rw [← bitIdx_eq]
  have hbs : ∀ j ∈ bitIdx m, j < 191 := fun j hj => lt_of_mem_bitIdx hj
  generalize bitIdx m = bs at hbs
  cases bs with
  | nil => rfl
  | cons i bs =>
    simp only [fixCntFrom]
    rw [countR_eq, getT_FLLT, fixLists_getD (hbs i List.mem_cons_self)]
    congr 1
    apply List.filter_congr
    intro c hc
    have hc' : c < 2048 := by
      rw [(fix_spec (hbs i List.mem_cons_self)).2] at hc
      exact List.mem_range.1 (List.mem_filter.1 hc).1
    rw [testBit_andAll FBT hc']
    simp only [getT_FBT]
    have hbs' : ∀ j ∈ bs, j < 191 := fun j hj => hbs j (List.mem_cons_of_mem _ hj)
    clear hc hbs
    induction bs with
    | nil => rfl
    | cons j bs ih =>
      rw [List.all_cons, List.all_cons, ih fun j' hj' => hbs' j' (List.mem_cons_of_mem _ hj'),
        inv_eq, (fix_spec (hbs' j List.mem_cons_self)).1 c hc']

theorem bound_of_mem {k : Nat} (hk : k < 8) {m : Nat} (hm : m ∈ LVk k) :
    m >>> 191 = 0 ∧ (m = 0 ∨ fixCntK FBT FLLT m * ((bitIdxK m).length + 1) ≤ 1024) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := LV_lens
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, -, -, -⟩ := trees
  interval_cases k
  · exact boundsChunk_spec r0 (nc := 1) (by rw [h0]; norm_num) bd_ok0 m hm
  · exact boundsChunk_spec r1 (nc := 1) (by rw [h1]; norm_num) bd_ok1 m hm
  · exact boundsChunk_spec r2 (nc := 5) (by rw [h2]; norm_num) bd_ok2 m hm
  · exact boundsChunk_spec r3 (nc := 8) (by rw [h3]; norm_num) bd_ok3 m hm
  · exact boundsChunk_spec r4 (nc := 3) (by rw [h4]; norm_num) bd_ok4 m hm
  · exact boundsChunk_spec r5 (nc := 1) (by rw [h5]; norm_num) bd_ok5 m hm
  · exact boundsChunk_spec r6 (nc := 1) (by rw [h6]; norm_num) bd_ok6 m hm
  · change m ∈ LV7 at hm
    rw [lv7_nil] at hm
    simp at hm

theorem chkFam_true : chkFam = true := by
  have h7 : levels.getD 7 [] = [] := by
    change lvl 7 = []
    apply List.eq_nil_iff_forall_not_mem.2
    intro m hm
    rw [mem_lvl 7 (by norm_num)] at hm
    change m ∈ LV7 at hm
    rw [lv7_nil] at hm
    simp at hm
  unfold chkFam
  rw [chkTabs_true, h7]
  simp only [List.isEmpty_nil, Bool.true_and, List.all_eq_true, Bool.and_eq_true, beq_iff_eq]
  intro L hL m hm
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hL
  have hk8 : k < 8 := by
    have := levelsFrom_length 8 [0]
    rw [levels] at hk
    omega
  have hm' : m ∈ lvl k := by
    rw [lvl, List.getD_eq_getElem _ _ hk]
    exact hm
  rw [mem_lvl k hk8] at hm'
  obtain ⟨hsh, hb⟩ := bound_of_mem hk8 hm'
  refine ⟨by rw [nInv_eq]; exact hsh, ?_⟩
  unfold boundOK
  rw [fixCnt_eq, bitIdx_eq]
  rcases hb with rfl | hb
  · rfl
  · simp [hb]

end CertificateChecks.KernelJ4Fam
