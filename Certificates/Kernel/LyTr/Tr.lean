module

public import Certificates.Kernel.LyTr.Glue
public import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLyTr

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KC.BfsPin
open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore
open CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Recognition.LyonsSims

theorem allRec_iff {n w cnt : Nat} {T PL : Nat → Nat} {p : Table → Bool} :
    (hRec n w cnt T PL).1.all p = true ↔ ∀ i < cnt, p (tabT (unpack n w (T i))) = true := by
  rw [Array.all_eq_true]
  constructor
  · intro h i hi
    have := h i (by simpa [hRec] using hi)
    simpa [hRec] using this
  · intro h i hi
    have hi' : i < cnt := by simpa [hRec] using hi
    simpa [hRec] using h i hi'

theorem mem_toList_get {a : Array Table} {T : Table} (h : T ∈ a.toList) :
    ∃ j < a.size, a[j]! = T := by
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem h
  have hj' : j < a.size := by simpa using hj
  exact ⟨j, hj', by rw [getElem!_pos a j hj']; simp⟩

theorem tab_ok {X Xi : Nat} (hX : C8 X) (hXi : C8 Xi) (h : i8 X Xi = true) :
    permOK 243 (tabT (unpack 243 8 X)) = true ∧
      invOK 243 (tabT (unpack 243 8 X)) (invT 243 (tabT (unpack 243 8 X))) = true := by
  rw [invT_unpack (by norm_num) h]
  exact ⟨permOK_unpack hX h, invOK_unpack hX hXi h⟩

theorem cj8_canon {g gi a : Nat} (hg : C8 g) (hgi : C8 gi) (ha : C8 a) : C8 (cj8 g gi a) :=
  canonK_pcomp (canonK_pcomp hg ha) hgi

theorem conjA_eq {g gi a : Nat} (hg : C8 g) (hgi : C8 gi) (ha : C8 a) :
    Ly243.conjA (tabT (unpack 243 8 g)) (tabT (unpack 243 8 gi)) (tabT (unpack 243 8 a)) =
      tabT (unpack 243 8 (cj8 g gi a)) :=
  conjT_unpack hg hgi ha

theorem inLine_eq {z a ai : Nat} (hz : C8 z) (ha : C8 a) (hai : C8 ai) :
    Ly243.inLine (tabT (unpack 243 8 z)) (tabT (unpack 243 8 a)) (tabT (unpack 243 8 ai)) =
      inL z a ai := by
  unfold Ly243.inLine inL
  rw [tblEq_unpack hz ha, tblEq_unpack hz hai]
  rfl

theorem gc {j : Nat} (hj : j < 5) : C8 (GH.F j) := (base8.2.2.2.1 j hj).1
theorem gic {j : Nat} (hj : j < 5) : C8 (GHI j) := (base8.2.2.2.1 j hj).2.1
theorem lc {j : Nat} (hj : j < 3) : C8 (LH.F j) := (base8.2.2.2.2.1 j hj).1
theorem lic {j : Nat} (hj : j < 3) : C8 (LHI j) := (base8.2.2.2.2.1 j hj).2.1
theorem tc {j : Nat} (hj : j < 5) : C8 (R2.GI j) := (base8.2.2.2.2.2.1 j hj).1
theorem tic {j : Nat} (hj : j < 5) : C8 (R2I j) := (base8.2.2.2.2.2.1 j hj).2.1
theorem rc {j : Nat} (hj : j < 6) : C8 (RP j) := (base8.2.2.2.2.2.2.1 j hj).1
theorem ric {j : Nat} (hj : j < 6) : C8 (RPI j) := (base8.2.2.2.2.2.2.1 j hj).2.1

theorem sz_gen : Ly243.genTabs.size = 5 := by simp [Ly243.genTabs]
theorem sz_line : Ly243.lineTabs.size = 3 := by simp [Ly243.lineTabs]
theorem sz_txy : Ly243.txyTabs.size = 5 := by
  have hs : Ly243.txyWords.length = 5 := by decide
  simp [Ly243.txyTabs, hs]
theorem sz_rep : Ly243.repTabs.size = 6 := by
  have hs : Ly243.repWords.length = 6 := by decide
  simp [Ly243.repTabs, hs]

theorem ordTest3 {j : Nat} (hj : j < 3) : ordTest 243 3 Ly243.lineTabs[j]! = ord8 3 (LH.F j) := by
  rw [lineT hj, ordTest_unpack (P := pw8 (LH.F j)) ⟨rfl, fun _ => rfl⟩
    (idK_sound base8.2.2.1).symm base8.2.1 (lc hj)]
  rfl

theorem tablesOK_of : Ly243.tablesOK = true := by
  have hl := k_lines
  simp only [bAnd_iff] at hl
  have hw : Ly243.wordsOK = true := by decide
  unfold Ly243.tablesOK Ly243.lineDataOK
  simp only [sz_gen, sz_line, sz_txy, sz_rep, hw, beq_self_eq_true, Bool.true_and,
    Bool.and_eq_true, List.all_eq_true, List.mem_append, List.mem_range]
  refine ⟨?_, ?_, ?_⟩
  · intro T hT
    rcases hT with ((hT | hT) | hT) | hT
    · obtain ⟨j, hj, rfl⟩ := mem_toList_get hT
      rw [sz_gen] at hj
      rw [genT hj]
      exact tab_ok (gc hj) (gic hj) (base8.2.2.2.1 j hj).2.2
    · obtain ⟨j, hj, rfl⟩ := mem_toList_get hT
      rw [sz_line] at hj
      rw [lineT hj]
      exact tab_ok (lc hj) (lic hj) (base8.2.2.2.2.1 j hj).2.2
    · obtain ⟨j, hj, rfl⟩ := mem_toList_get hT
      rw [sz_txy] at hj
      rw [txy243T hj]
      exact tab_ok (tc hj) (tic hj) (base8.2.2.2.2.2.1 j hj).2.2.1
    · obtain ⟨j, hj, rfl⟩ := mem_toList_get hT
      rw [sz_rep] at hj
      rw [repT hj]
      exact tab_ok (rc hj) (ric hj) (base8.2.2.2.2.2.2.1 j hj).2.2
  · intro i hi
    rw [ordTest3 hi]
    exact allN_spec hl.1 i hi
  · intro i hi j hj
    have h := allN_spec (allN_spec hl.2 i hi) j hj
    rw [lineT hj, lineT hi, lineIT hi, inLine_eq (lc hj) (lc hi) (lic hi)]
    by_cases hij : i = j
    · simp [hij]
    · have hb : Nat.beq i j = false := Bool.eq_false_iff.2 fun e => hij (Nat.eq_of_beq_eq_true e)
      rw [hb] at h
      simpa [hij] using h

theorem any3 {f : Nat → Bool} (h : bIf(f 0, true, bIf(f 1, true, f 2)) = true) :
    (List.range 3).any f = true := by
  rw [List.any_eq_true]
  cases h0 : f 0
  · cases h1 : f 1
    · rw [h0, h1] at h
      exact ⟨2, by simp, h⟩
    · exact ⟨1, by simp, h1⟩
  · exact ⟨0, by simp, h0⟩

theorem permutesOK_of : Ly243.permutesOK = true := by
  unfold Ly243.permutesOK
  rw [List.all_eq_true]
  intro m hm
  have hm' : m < 5 := List.mem_range.1 hm
  rw [List.all_eq_true]
  intro i hi
  have hi' : i < 3 := List.mem_range.1 hi
  apply any3
  have h := allN_spec (allN_spec k_perm m hm') i hi'
  rw [genT hm', genIT hm', lineT hi', conjA_eq (gc hm') (gic hm') (lc hi')]
  have c := cj8_canon (gc hm') (gic hm') (lc hi')
  rw [lineT (by norm_num : 0 < 3), lineIT (by norm_num : 0 < 3), lineT (by norm_num : 1 < 3),
    lineIT (by norm_num : 1 < 3), lineT (by norm_num : 2 < 3), lineIT (by norm_num : 2 < 3),
    inLine_eq c (lc (by norm_num)) (lic (by norm_num)), inLine_eq c (lc (by norm_num)) (lic (by norm_num)),
    inLine_eq c (lc (by norm_num)) (lic (by norm_num))]
  exact h

theorem fixZeroOK_of : Ly243.fixZeroOK = true := by
  unfold Ly243.fixZeroOK
  rw [List.all_eq_true]
  intro m hm
  have hm' : m < 4 := List.mem_range.1 hm
  have h5 : m < 5 := by omega
  rw [genT h5, genIT h5, lineT (by norm_num : 0 < 3), lineIT (by norm_num : 0 < 3),
    conjA_eq (gc h5) (gic h5) (lc (by norm_num)),
    inLine_eq (cj8_canon (gc h5) (gic h5) (lc (by norm_num))) (lc (by norm_num)) (lic (by norm_num))]
  exact allN_spec k_fix0 m hm'

theorem kSwapOK_of : Ly243.kSwapOK = true := by
  have h := k_kswap
  simp only [bAnd_iff] at h
  have c4 := gc (by norm_num : 4 < 5)
  have ci4 := gic (by norm_num : 4 < 5)
  unfold Ly243.kSwapOK
  rw [genT (by norm_num), genIT (by norm_num), lineT (by norm_num : 0 < 3),
    lineIT (by norm_num : 0 < 3), lineT (by norm_num : 1 < 3), lineIT (by norm_num : 1 < 3),
    lineT (by norm_num : 2 < 3), lineIT (by norm_num : 2 < 3),
    conjA_eq c4 ci4 (lc (by norm_num)), conjA_eq c4 ci4 (lc (by norm_num)),
    conjA_eq c4 ci4 (lc (by norm_num)),
    inLine_eq (cj8_canon c4 ci4 (lc (by norm_num))) (lc (by norm_num)) (lic (by norm_num)),
    inLine_eq (cj8_canon c4 ci4 (lc (by norm_num))) (lc (by norm_num)) (lic (by norm_num)),
    inLine_eq (cj8_canon c4 ci4 (lc (by norm_num))) (lc (by norm_num)) (lic (by norm_num)),
    h.1, h.2.1, h.2.2]
  rfl

theorem txyKerOK_of : Ly243.txyKerOK = true := by
  unfold Ly243.txyKerOK
  rw [List.all_eq_true]
  intro j hj
  have hj' : j < 5 := List.mem_range.1 hj
  rw [List.all_eq_true]
  intro i hi
  have hi' : i < 3 := List.mem_range.1 hi
  rw [txy243T hj', txy243IT hj', lineT hi', lineIT hi', conjA_eq (tc hj') (tic hj') (lc hi'),
    inLine_eq (cj8_canon (tc hj') (tic hj') (lc hi')) (lc hi') (lic hi')]
  exact allN_spec (allN_spec k_ker j hj') i hi'

theorem txy_tabs : TabsOK 243 8 5 R2.GI Ly243.txyTabs.toList.toArray := by
  rw [Array.toArray_toList]
  exact ⟨sz_txy, fun j hj => ⟨txy243T hj, tc hj⟩⟩

theorem txy_invs : ∀ j < 5, invEqK 243 8 (mask 8) (243 * 8) (R2.GI j) (R2I j) = true ∧
    canonK 243 8 (mask 8) (243 * 8) (R2I j) = true :=
  fun j hj => ⟨(base8.2.2.2.2.2.1 j hj).2.2.1, tic hj⟩

theorem r2G : ∀ j < 5, R2.G j = pidn 243 8 := fun j hj => (base8.2.2.2.2.2.1 j hj).2.2.2

theorem r2clSl_all : ∀ s < 16, r2clSl s = true := by
  intro s hs
  interval_cases s
  exacts [k_r2cl0, k_r2cl1, k_r2cl2, k_r2cl3, k_r2cl4, k_r2cl5, k_r2cl6, k_r2cl7, k_r2cl8, k_r2cl9,
    k_r2cl10, k_r2cl11, k_r2cl12, k_r2cl13, k_r2cl14, k_r2cl15]

theorem r2_cl : ∀ c < R2.cnt * (5 + 5), findPtK R2.cnt R2.T
    (prodQK 243 8 (mask 8) (5 + 5) R2.T (bothK 5 R2.GI R2I)) R2Cl c = true := by
  intro c hc
  have hn : R2.cnt = 3888 := base8.2.2.2.2.2.2.2.1
  have hs := r2clSl_all (c / 2430) (by rw [hn] at hc; omega)
  exact slK_spec hs c (by omega) (by omega) (by change c < Nat.mul R2.cnt 10; omega)

theorem txyEnumOK_of : Ly243.txyEnumOK = true :=
  enumOK_of base8.1 r2G txy_tabs txy_invs base8.2.2.2.2.2.2.2.2 r2_pe r2_hs r2_cl base8.2.2.2.2.2.2.2.1

theorem txyEnum_eq : Ly243.txyEnum = hRec 243 8 R2.cnt R2.T R2.PL :=
  (mulH_sound base8.1 r2G txy_tabs base8.2.2.2.2.2.2.2.2 r2_pe r2_hs).1

theorem r2c {i : Nat} (hi : i < R2.cnt) : C8 (R2.T i) := penumPt_canon (r2_pe i hi)

theorem txyCenterOK_of : Ly243.txyCenterOK = true := by
  unfold Ly243.txyCenterOK
  rw [txyEnum_eq, allRec_iff]
  intro i hi
  have hc := r2c hi
  have hk : centAt (R2.T i) = true := by
    have h4 := base8.2.2.2.2.2.2.2.1
    have hs : i / 972 < 4 := by omega
    have h1 : 972 * (i / 972) ≤ i := Nat.mul_div_le i 972
    have h2 : i < 972 * (i / 972) + 972 := by omega
    generalize i / 972 = s at hs h1 h2
    interval_cases s
    · exact slK_spec k_cent0 i (by omega) (by omega) hi
    · exact slK_spec k_cent1 i (by omega) (by omega) hi
    · exact slK_spec k_cent2 i (by omega) (by omega) hi
    · exact slK_spec k_cent3 i (by omega) (by omega) hi
  unfold centAt at hk
  have hall : (Ly243.txyTabs.all fun g => commTT 243 (tabT (unpack 243 8 (R2.T i))) g) =
      allN 5 (fun g => Nat.beq (p8 (R2.T i) (R2.GI g)) (p8 (R2.GI g) (R2.T i))) := by
    rw [Bool.eq_iff_iff, Array.all_eq_true, CFSG.KS.Raw.Orb.allN_iff]
    constructor
    · intro h g hg
      have e := h g (by rw [sz_txy]; exact hg)
      rw [← getElem!_pos _ g (by rw [sz_txy]; exact hg), txy243T hg, commTT_unpack hc (tc hg)] at e
      exact e
    · intro h g hg
      have hg' : g < 5 := by rw [← sz_txy]; exact hg
      rw [← getElem!_pos _ g hg, txy243T hg', commTT_unpack hc (tc hg')]
      exact h g hg'
  rw [hall, hid8, tblEq_unpack hc base8.2.1]
  revert hk
  cases allN 5 (fun g => Nat.beq (p8 (R2.T i) (R2.GI g)) (p8 (R2.GI g) (R2.T i))) <;> simp

theorem GB_eq {m : Nat} (hm : m < 10) :
    (Ly243.genTabs.toList ++ Ly243.genInvTabs.toList).getD m #[] = tabT (unpack 243 8 (GB m)) ∧
      C8 (GB m) := by
  have hs : Ly243.genTabs.toList.length = 5 := by simp [sz_gen]
  have hsi : Ly243.genInvTabs.toList.length = 5 := by simp [Ly243.genInvTabs, sz_gen]
  by_cases h : m < 5
  · have e : GB m = GH.F m := by
      unfold GB
      rw [Nat.blt_eq.mpr h]
    rw [e, List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [hs]; exact h),
      Array.getElem?_toList]
    rw [getElem?_pos _ m (by rw [sz_gen]; exact h), Option.getD_some, ← getElem!_pos _ m
      (by rw [sz_gen]; exact h), genT h]
    exact ⟨rfl, gc h⟩
  · have hb : Nat.blt m 5 = false := Bool.eq_false_iff.2 fun e => h (Nat.blt_eq.mp e)
    have e : GB m = GHI (m - 5) := by
      unfold GB
      rw [hb]
    have h5 : m - 5 < 5 := by omega
    rw [e, List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [hs]; omega), hs,
      Array.getElem?_toList]
    rw [getElem?_pos _ (m - 5) (by simp [Ly243.genInvTabs, sz_gen]; exact h5), Option.getD_some,
      ← getElem!_pos _ (m - 5) (by simp [Ly243.genInvTabs, sz_gen]; exact h5), genIT h5]
    exact ⟨rfl, gic h5⟩

theorem mem_gens {g : Table} (hg : g ∈ Ly243.genTabs.toList ++ Ly243.genInvTabs.toList) :
    ∃ m < 10, g = tabT (unpack 243 8 (GB m)) ∧ C8 (GB m) := by
  have hl : (Ly243.genTabs.toList ++ Ly243.genInvTabs.toList).length = 10 := by
    simp [Ly243.genInvTabs, sz_gen]
  obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hg
  have hm' : m < 10 := by rw [← hl]; exact hm
  refine ⟨m, hm', ?_⟩
  have e := GB_eq hm'
  rw [List.getD_eq_getElem?_getD, getElem?_pos _ m hm, Option.getD_some] at e
  exact e

theorem cos_spec {i m : Nat} (hi : i < 6) (hm : m < 10) :
    cjOf (i * 10 + m) < 6 ∧ r32 CP (i * 10 + m) < R2.cnt ∧
      R2.T (r32 CP (i * 10 + m)) = p8 (p8 (RP i) (GB m)) (RPI (cjOf (i * 10 + m))) := by
  have h := k_coset
  simp only [bAnd_iff] at h
  have hc := allN_spec h.2.1 (i * 10 + m) (by omega)
  simp only [bAnd_iff, Nat.blt_eq] at hc
  obtain ⟨hq, he⟩ := findPt_spec hc.2
  obtain ⟨e1, e2⟩ := div_mod_pair (i := i) (K := 10) hm
  unfold cosQ at he
  rw [show Nat.div (i * 10 + m) 10 = i from e1, show Nat.mod (i * 10 + m) 10 = m from e2] at he
  exact ⟨hc.1, hq, he⟩

theorem fixesLines_eq {j : Nat} (hj : j < 6) :
    Ly243.fixesLines Ly243.repTabs[j]! = fixL (RP j) (RPI j) := by
  unfold Ly243.fixesLines fixL
  rw [repT hj, invT_unpack (by norm_num) (base8.2.2.2.2.2.2.1 j hj).2.2, Bool.eq_iff_iff,
    List.all_eq_true, CFSG.KS.Raw.Orb.allN_iff]
  refine forall_congr' fun i => ?_
  constructor
  · intro h hi
    have hi' := h (List.mem_range.2 hi)
    rw [lineT hi, lineIT hi, conjA_eq (rc hj) (ric hj) (lc hi),
      inLine_eq (cj8_canon (rc hj) (ric hj) (lc hi)) (lc hi) (lic hi)] at hi'
    exact hi'
  · intro h hi
    have hi' := List.mem_range.1 hi
    rw [lineT hi', lineIT hi', conjA_eq (rc hj) (ric hj) (lc hi'),
      inLine_eq (cj8_canon (rc hj) (ric hj) (lc hi')) (lc hi') (lic hi')]
    exact h hi'

theorem cosetOK_of : Ly243.cosetOK = true := by
  have h := k_coset
  simp only [bAnd_iff] at h
  obtain ⟨h0, -, h2⟩ := h
  unfold Ly243.cosetOK
  simp only [Bool.and_eq_true, List.all_eq_true, List.any_eq_true, List.mem_range]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [repT (by norm_num), hid8, tblEq_unpack (rc (by norm_num)) base8.2.1]
    exact h0
  · intro i hi g hg
    obtain ⟨m, hm, rfl, hgc⟩ := mem_gens hg
    obtain ⟨hj, hq, he⟩ := cos_spec hi hm
    refine ⟨cjOf (i * 10 + m), hj, ?_⟩
    rw [repT hi, repT hj, invT_unpack (by norm_num) (base8.2.2.2.2.2.2.1 _ hj).2.2,
      compT_unpack (rc hi) hgc, compT_unpack (canonK_pcomp (rc hi) hgc) (ric hj),
      txyEnum_eq]
    refine memT_of hq ?_
    rw [he]
    exact tblEq_self (canonK_pcomp (canonK_pcomp (rc hi) hgc) (ric hj))
  · intro j hj
    by_cases e : j = 0
    · subst e
      rfl
    · have hb : (j == 0) = false := by simp [e]
      rw [hb, Bool.false_or, fixesLines_eq hj]
      have := allN_spec h2 (j - 1) (by omega)
      rw [show j - 1 + 1 = j by omega] at this
      exact this

theorem sigmaWords_ok : ∀ j < 5, ∀ l ∈ Ly1080.sigmaTxyWords.getD j [], l ≠ 0 ∧ l.natAbs ≤ 5 := by
  decide

theorem kCompatOK_of : Ly243.kCompatOK = true := by
  have hs : Ly1080.sigmaTxyWords.length = 5 := by decide
  unfold Ly243.kCompatOK
  simp only [hs, beq_self_eq_true, Bool.true_and, List.all_eq_true, List.mem_range]
  intro j hj
  have hw := wordT_eqK hid8 base8.2.1 (gens := Ly243.txyLet) (G := LT)
    (Ly1080.sigmaTxyWords.getD j []) fun l hl =>
      txyLetT (sigmaWords_ok j hj l hl).1 (sigmaWords_ok j hj l hl).2
  have e : Ly1080.sigmaTxyWords[j]! = Ly1080.sigmaTxyWords.getD j [] := by
    simp [List.getD_eq_getElem?_getD, getElem!_def, hs, hj]
  have c4 := gc (by norm_num : 4 < 5)
  have ci4 := gic (by norm_num : 4 < 5)
  rw [e, hw.1, genT (by norm_num), genIT (by norm_num), txy243T hj, conjT_unpack c4 ci4 (tc hj),
    tblEq_unpack (p := pcomp 243 8 (mask 8) (pcomp 243 8 (mask 8) (GH.F 4) (R2.GI j)) (GHI 4))
      (cj8_canon c4 ci4 (tc hj)) hw.2]
  exact allN_spec k_kcompat j hj

end CertificateChecks.KernelLyTr

end
