module

public import Certificates.Kernel.SmithD6UwB.Facts
public import Certificates.Kernel.SmithD6Uw.Glue
public import Certificates.Kernel.SmithD6Kc.Facts
import all Certificates.Data.SmithD6Uw
import all Certificates.Kernel.SmithD6UwB.Facts

set_option maxRecDepth 100000

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CertificateChecks.SmithD6UwB

open CFSG.SmithD6 CFSG.KC.KeyTree CFSG.KC.PkTree CFSG.KD.SmithD6
  CFSG.GF2Type.SmithTypeE.DMod CertificateChecks.SmithD6Wt CertificateChecks.SmithD6Uw

theorem rhoC_eV {i : ℕ} (hi : i < 6) (s : ℕ) : rhoC (eV i) s = wedC i s := by
  unfold rhoC eV
  interval_cases i <;> simp (config := { decide := true }) [xorFold_succ, xorFold_zero]

theorem testBit_of_decode64_eq_zero {c : ℕ} (h : decode64 c = 0) (T : Fin 64) :
    c.testBit T.val = false := by
  have h1 := congrFun h T
  rw [decode64_apply] at h1
  cases hc : c.testBit T.val
  · rfl
  · rw [hc] at h1
    simp [bit] at h1

theorem flip_facts : ∀ T : Fin 64, T.val ≠ 63 →
    ∃ i : Fin 6, T.val.testBit i.val = false ∧ (flipS i T).val.testBit i.val = true := by
  decide

theorem ubTop_eq : ubTop = 2 ^ 63 := by decide

theorem eq_top_of_wedC {s : ℕ} (hs : s < 2 ^ 64) (h63 : s.testBit 63 = true)
    (h : ∀ i : Fin 6, ∀ T : Fin 64, (wedC i.val s).testBit T.val = false) : s = ubTop := by
  rw [ubTop_eq]
  apply Nat.eq_of_testBit_eq
  intro T
  rw [Nat.testBit_two_pow]
  by_cases hT : T < 64
  · by_cases hT63 : T = 63
    · subst hT63
      rw [h63]
      rfl
    · obtain ⟨i, -, hb⟩ := flip_facts ⟨T, hT⟩ hT63
      have key := h i (flipS i ⟨T, hT⟩)
      rw [testBit_wedC, flipS_flipS, hb, Bool.true_and] at key
      rw [key]
      exact (decide_eq_false fun e => hT63 e.symm).symm
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hs (Nat.pow_le_pow_right (by norm_num)
      (by omega)))]
    exact (decide_eq_false fun e => hT (by omega)).symm

theorem memR_of_planeL {s : ℕ} {B P : Array ℕ} (hs : s < 2 ^ 64)
    (h : planeL s B.toList P.toList = true) {x : ℕ} (hx : x < 4096) (hr : rhoC x s = 0) :
    memR B P x = true := by
  have hmem : dec12 x ∈ planeSpan B := by
    rw [planeSpan_eq_annSub_of_planeL hs h, mem_annSub, ← decode64_rhoC, hr, decode64_zero]
  obtain ⟨d, hd, hdx⟩ := mem_planeSpan_iff.1 hmem
  obtain ⟨-, -, -, hann, hpiv⟩ := planeL_sound h
  have hB : ∀ m < 6, B[m]! < 4096 := fun m hm => by
    refine (hann _ ?_).1
    rw [getElem!_eq_getD_toList, List.getD_eq_getElem _ _ (by
      rw [(planeL_sound h).2.1]; exact hm)]
    exact List.getElem_mem _
  have hxe : x = xorComb B d := eq_of_dec12_eq hx (xorComb_lt hB d) hdx
  rcases P with ⟨ps⟩
  have hp : ∀ j < 6, ∀ k < 6, B[k]!.testBit (ps.getD j 0) = (k == j) := fun j hj k hk => by
    rw [getElem!_eq_getD_toList]
    exact hpiv j hj k hk
  have hc : coefOf ⟨ps⟩ (xorComb B d) = d := by
    apply Nat.eq_of_testBit_eq
    intro m
    by_cases hm : m < 6
    · rw [testBit_coefOf _ hm]
      exact testBit_xorComb_piv (p := fun j => ps.getD j 0) hp d hm
    · have h64 : (64 : ℕ) ≤ 2 ^ m := by
        have := Nat.pow_le_pow_right (n := 2) (by norm_num) (by omega : 6 ≤ m)
        simpa using this
      rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (coefOf_lt _ _) h64),
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hd h64)]
  unfold memR
  rw [hxe, hc]
  exact beq_self_eq_true _

theorem planeL_flat {j : ℕ} (hj : j < 75735) :
    planeL (J.wt64C.flatten.getD j 0) (J.pbC.flatten.getD j #[]).toList
      (J.ppC.flatten.getD j #[]).toList = true := by
  obtain ⟨e1, e2, hk⟩ := SmithD6Kc.pb_flat_getD hj
  have hc : j / 2048 < 37 := by omega
  obtain ⟨h1, h2, h3⟩ := planes (j / 2048) hc
  have hl : J.wt64C.length = 37 := wt64C_length
  have hk' : j % 2048 < (J.wt64C.getD (j / 2048) []).length := by rw [← h1]; exact hk
  have hlen : ∀ c, c + 1 < J.wt64C.length → (J.wt64C.getD c []).length = 2048 := by
    intro c hc'
    rw [hl] at hc'
    have hc37 : c < 37 := by omega
    rw [← (planes c hc37).1, (SmithD6Kc.pbC_chunk_length hc37).1, if_pos hc']
  have e3 : J.wt64C.flatten.getD j 0 = (J.wt64C.getD (j / 2048) []).getD (j % 2048) 0 := by
    have e : 2048 * (j / 2048) + j % 2048 = j := Nat.div_add_mod j 2048
    rw [← SmithD6Kc.flatten_getD_chunk 0 2048 J.wt64C hlen _ _ (by rw [hl]; exact hc) hk', e]
  rw [e1, e2, e3]
  exact h3 _ hk'

theorem fB_top_left (v : ℕ) : fB (2 ^ 31) v = v.testBit 0 := by
  have key : ∀ n, n ≤ 32 →
      (List.range n).foldl (fun b t => b ^^ ((2 ^ 31 : ℕ).testBit t && v.testBit (31 - t))) false =
        (decide (31 < n) && v.testBit 0) := by
    intro n hn
    induction n with
    | zero => simp
    | succ n ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih (by omega),
        Nat.testBit_two_pow]
      by_cases h : n = 31
      · subst h
        cases v.testBit 0 <;> decide
      · have hd : decide (31 = n) = false := decide_eq_false fun e => h e.symm
        rw [hd, Bool.false_and, Bool.xor_false]
        by_cases h2 : 31 < n
        · simp [h2, show 31 < n + 1 by omega]
        · simp [h2, show ¬ 31 < n + 1 by omega]
  exact (key 32 le_rfl).trans (by simp)

theorem testBit_exC_0 (s : ℕ) : (exC s).testBit 0 = s.testBit 0 := by
  have he : ∀ c : Fin 32, (evF c).val = 0 ↔ c = 0 := by decide +kernel
  rw [testBit_exC]
  by_cases hs : s.testBit 0 = true
  · rw [hs]
    exact decide_eq_true ⟨0, (he 0).2 rfl, hs⟩
  · rw [Bool.eq_false_iff.2 hs]
    refine decide_eq_false fun ⟨c, hc, hc'⟩ => hs ?_
    rw [(he c).1 hc] at hc'
    exact hc'

theorem exC_top : exC (2 ^ 31) = ubTop := by decide +kernel

theorem rhoC_eV_top : ∀ i : Fin 6, rhoC (eV i.val) ubTop = 0 := by decide +kernel

theorem applyCols_of_rho {k x y u w : ℕ} (hl : linePair k = (u, w)) (hy : y < 2 ^ 32)
    (h : exC x ^^^ rhoC u (rhoC w (exC x)) = exC y) : applyCols (tvCols k) x = y := by
  apply eq_of_decode32_eq (applyCols_tvCols_lt k x) hy
  apply exL_injective
  rw [decode32_applyCols (tvCols_size k), exL_colsLin_tvCols, hl, ← decode64_exC, ← decode64_exC,
    ← h, decode64_xor, decode64_rhoC, decode64_rhoC]
  rfl

theorem bE0_facts : JB.bE0 < 75735 ∧ ∃ h : JB.bE0 < J.wtC.flatten.length,
    J.wtC.flatten[JB.bE0] = 2 ^ 31 := by
  obtain ⟨h1, h2⟩ := ubE0
  have hn64 := wt64_facts.2.1
  have hl : JB.bE0 < J.wtC.flatten.length := by rw [wtC_flatten_length]; rw [hn64] at h1; exact h1
  refine ⟨by rw [hn64] at h1; exact h1, hl, ?_⟩
  rw [wt64_get h1] at h2
  exact exC_inj (wtC_lt hl) (by norm_num) (h2.trans exC_top.symm)

theorem pos_inj {a b : ℕ} (ha : a < J.wt64C.flatten.length) (hb : b < J.wt64C.flatten.length)
    (h : J.wt64C.flatten[a] = J.wt64C.flatten[b]) : a = b := by
  have h1 := wt64_facts.2.2.1 a ha
  have h2 := wt64_facts.2.2.1 b hb
  rw [h] at h1
  omega

section Model

variable (hW : wtArr.toList = J.wtC.flatten)
  (hpb : ∀ i < 75735, pbArr[i]! = J.pbC.flatten.getD i #[])
  (hpp : ∀ i < 75735, ppArr[i]! = J.ppC.flatten.getD i #[])

include hW in
theorem wt64_wt {j : ℕ} (hj : j < 75735) : J.wt64C.flatten.getD j 0 = exC (wt j) := by
  have hjl : j < J.wtC.flatten.length := by rw [wtC_flatten_length]; exact hj
  rw [wt64_getD, wt_eq hW hjl, List.getD_eq_getElem _ _ hjl]

include hW in
theorem fB_wt0 (j : ℕ) : fB (wt 0) (wt j) = (exC (wt j)).testBit 63 := by
  obtain ⟨h0l, h0⟩ := wt0
  rw [wt_eq hW h0l, h0, fB_one_left, testBit_exC_63]

include hW hpb hpp in
theorem e0_pred_iff {j : ℕ} (hj : j < 75735) :
    (fB (wt 0) (wt j) && (List.range 6).all fun i => memR pbArr[j]! ppArr[j]! (eV i)) = true ↔
      j = JB.bE0 := by
  have hn64 := wt64_facts.2.1
  have hP := planeL_flat hj
  rw [wt64_wt hW hj] at hP
  have hs : exC (wt j) < 2 ^ 64 := exC_lt_two_pow _
  rw [fB_wt0 hW, hpb j hj, hpp j hj]
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range]
  constructor
  · rintro ⟨h63, hm⟩
    have htop : exC (wt j) = ubTop := by
      refine eq_top_of_wedC hs h63 fun i T => ?_
      have h1 := dec12_mem_planeSpan_of_memR (hm i.val i.isLt)
      rw [planeSpan_eq_annSub_of_planeL hs hP, mem_annSub, ← decode64_rhoC,
        rhoC_eV i.isLt] at h1
      exact testBit_of_decode64_eq_zero h1 T
    obtain ⟨hE, hEx⟩ := ubE0
    have hj64 : j < J.wt64C.flatten.length := by rw [hn64]; exact hj
    refine pos_inj hj64 hE ?_
    rw [hEx, ← htop, ← wt64_wt hW hj, List.getD_eq_getElem _ _ hj64]
  · rintro rfl
    obtain ⟨hE, hEx⟩ := ubE0
    have htop : exC (wt JB.bE0) = ubTop := by
      rw [← wt64_wt hW hj, List.getD_eq_getElem _ _ hE, hEx]
    rw [htop] at hP ⊢
    refine ⟨by decide, fun i hi => ?_⟩
    exact memR_of_planeL (by rw [ubTop_eq]; norm_num) hP
      (by unfold eV; exact lt_of_lt_of_le (Nat.pow_lt_pow_right (by norm_num) hi) (by norm_num))
      (rhoC_eV_top ⟨i, hi⟩)

include hW hpb hpp in
theorem uw7E0_eq : uw7E0 () = JB.bE0 := by
  have hlt := bE0_facts.1
  unfold uw7E0
  rw [CertificateChecks.SmithD6Stab.find?_range hlt ((e0_pred_iff hW hpb hpp hlt).2 rfl)
    fun a ha => Bool.eq_false_iff.2 fun h =>
      Nat.ne_of_lt ha ((e0_pred_iff hW hpb hpp (Nat.lt_trans ha hlt)).1 h)]
  rfl

include hW hpb hpp in
theorem uw7ChkE0_of_pinned : uw7ChkE0 () = true := by
  have hlt := bE0_facts.1
  have h := (e0_pred_iff hW hpb hpp hlt).2 rfl
  unfold uw7ChkE0
  rw [uw7E0_eq hW hpb hpp]
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h ⊢
  exact ⟨⟨hlt, h.1⟩, h.2⟩

include hW in
theorem ubK_model {j : ℕ} (hj : j < 75735) :
    pkGet JB.bK 2 j = if uw7InB JB.bE0 j = true then uw7BCls JB.bE0 j else 0 := by
  obtain ⟨-, hn64, hf64, hs64⟩ := wt64_facts
  obtain ⟨-, hEl, hEx⟩ := bE0_facts
  have hjl : j < J.wtC.flatten.length := by rw [wtC_flatten_length]; exact hj
  have hjl64 : j < J.wt64C.flatten.length := by rw [hn64]; exact hj
  have hsj := wtC_lt hjl
  have hmemj := List.getElem_mem hjl
  rw [ubK_eq j hjl64, wt64_get hjl64]
  unfold uw7InB uw7BCls adjW
  rw [fB_wt0 hW, wt_eq hW hjl, wt_eq hW hEl, hEx]
  have hiff : (j != JB.bE0) = (J.wtC.flatten[j]'hjl != 2 ^ 31) := by
    rw [Bool.eq_iff_iff, bne_iff_ne, bne_iff_ne, ne_eq, ne_eq, not_iff_not]
    constructor
    · rintro rfl
      exact hEx
    · intro e
      have h1 := wtIdx_get hW hjl
      have h2 := wtIdx_get hW hEl
      rw [e] at h1
      rw [hEx] at h2
      omega
  rw [hiff]
  generalize J.wtC.flatten[j]'hjl = s at hsj hmemj ⊢
  by_cases hne : s = 2 ^ 31
  · subst hne
    rw [exC_top, bne_self_eq_false, Bool.and_false, if_neg Bool.false_ne_true]
    unfold ubKOf
    rw [fld_one_eq, show ubTop.testBit 63 = true by decide, Nat.beq_refl]
    rfl
  have hbne : (s != 2 ^ 31) = true := bne_iff_ne.2 hne
  rw [hbne, Bool.and_true]
  have htop : Nat.beq (exC s) ubTop = false := by
    refine Bool.eq_false_iff.2 fun h => hne ?_
    exact exC_inj hsj (by norm_num) ((Nat.eq_of_beq_eq_true h).trans exC_top.symm)
  have hmem : KT.memB (Nat.xor ubTop (exC s)) wt64Tree = decide (wtIdx (2 ^ 31 ^^^ s) < 75735) := by
    have hx : Nat.xor ubTop (exC s) = exC (2 ^ 31 ^^^ s) := by
      rw [exC_xor, exC_top]
      rfl
    rw [hx, Bool.eq_iff_iff, memB_iff_mem hf64 hs64, decide_eq_true_iff, wtIdx_lt_iff hW,
      wt64_eq_map.1]
    constructor
    · intro h
      obtain ⟨y, hy, hyx⟩ := List.mem_map.1 h
      rwa [← exC_inj (wtC_lt_mem hy) (Nat.xor_lt_two_pow (by norm_num) hsj) hyx]
    · intro h
      exact List.mem_map_of_mem h
  have hb63 : Nat.beq (Nat.land (Nat.shiftRight (exC s) 63) 1) 1 = (exC s).testBit 63 := by
    rw [fld_one_eq]
    cases (exC s).testBit 63 <;> rfl
  have hb0 : Nat.beq (Nat.land (Nat.shiftRight (exC s) 0) 1) 1 = s.testBit 0 := by
    rw [fld_one_eq, testBit_exC_0]
    cases s.testBit 0 <;> rfl
  have hb1 : (2 ^ 31 == s) = false := by
    rw [beq_eq_false_iff_ne]
    exact fun e => hne e.symm
  rw [fB_top_left, hb1, Bool.false_or]
  unfold ubKOf ubClsK
  rw [hb63, htop, hb0, hmem]
  cases (exC s).testBit 63 <;> cases s.testBit 0 <;> cases decide (wtIdx (2 ^ 31 ^^^ s) < 75735) <;>
    rfl

theorem uw7BCls_pos (e0 j : ℕ) : uw7BCls e0 j ≠ 0 := by
  unfold uw7BCls
  split_ifs <;> simp

theorem uw7BCls_le (e0 j : ℕ) : uw7BCls e0 j ≤ 3 := by
  unfold uw7BCls
  split_ifs <;> simp

include hW in
theorem inB_iff {j : ℕ} (hj : j < 75735) : uw7InB JB.bE0 j = true ↔ pkGet JB.bK 2 j ≠ 0 := by
  rw [ubK_model hW hj]
  by_cases h : uw7InB JB.bE0 j = true
  · rw [if_pos h]
    exact ⟨fun _ => uw7BCls_pos _ _, fun _ => h⟩
  · rw [if_neg h]
    exact ⟨fun h' => absurd h' h, fun h' => absurd rfl h'⟩

include hW in
theorem bkey {j : ℕ} (hj : j < 75735) (c : ℕ) :
    (uw7InB JB.bE0 j && uw7BCls JB.bE0 j == c + 1) = (pkGet JB.bK 2 j == c + 1) := by
  rw [ubK_model hW hj]
  by_cases h : uw7InB JB.bE0 j = true
  · rw [if_pos h, h, Bool.true_and]
  · rw [if_neg h, Bool.eq_false_iff.2 h, Bool.false_and]
    exact (beq_eq_false_iff_ne.2 (by omega)).symm

include hW hpb hpp in
theorem uw7BReps_eq {c : ℕ} (hc : c < 3) : (uw7BReps ())[c]! = ubRep (c + 1) := by
  obtain ⟨-, hR⟩ := ubReps
  have hc' : c + 1 ∈ [1, 2, 3] := by
    rcases (show c = 0 ∨ c = 1 ∨ c = 2 by omega) with rfl | rfl | rfl <;> simp
  obtain ⟨hlt, hcls⟩ := hR (c + 1) hc'
  have hn64 := wt64_facts.2.1
  have hfirst : ∀ a < ubRep (c + 1),
      (uw7InB JB.bE0 a && uw7BCls JB.bE0 a == c + 1) = false := by
    intro a ha
    have ha' : a < 75735 := Nat.lt_trans ha hlt
    rw [bkey hW ha', beq_eq_false_iff_ne]
    intro h
    have := ubFirst a (by rw [hn64]; exact ha') (by rw [h]; omega)
    rw [h] at this
    omega
  have hf := CertificateChecks.SmithD6Stab.find?_range
    (p := fun a => uw7InB JB.bE0 a && uw7BCls JB.bE0 a == c + 1) hlt
    (by simp only [bkey hW hlt, hcls, beq_self_eq_true]) hfirst
  unfold uw7BReps
  rw [uw7E0_eq hW hpb hpp, getElem!_pos]
  all_goals simp [hc, hf]

include hW hpb hpp in
theorem uw7ChkBCls_of_pinned : uw7ChkBCls () = true := by
  obtain ⟨-, hR⟩ := ubReps
  obtain ⟨-, n1, n2, n3⟩ := ubCnt_vals
  have hcnt : ∀ c, ((List.range 75735).filter fun j =>
      uw7InB JB.bE0 j && uw7BCls JB.bE0 j == c + 1).length = ubCnt (c + 1) := by
    intro c
    rw [ubCnt_eq]
    congr 1
    apply List.filter_congr
    intro j hj
    rw [bkey hW (List.mem_range.1 hj)]
  have hsize : (uw7BReps ()).size = 3 := by
    unfold uw7BReps
    simp
  unfold uw7ChkBCls
  rw [uw7E0_eq hW hpb hpp]
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range, decide_eq_true_eq]
  refine ⟨⟨hsize, fun c hc => ?_⟩, fun c hc => ?_⟩
  · have hc' : c + 1 ∈ [1, 2, 3] := by
      rcases (show c = 0 ∨ c = 1 ∨ c = 2 by omega) with rfl | rfl | rfl <;> simp
    obtain ⟨hlt, hcls⟩ := hR (c + 1) hc'
    rw [uw7BReps_eq hW hpb hpp hc]
    have hk := bkey hW hlt c
    rw [hcls, beq_self_eq_true, Bool.and_eq_true, beq_iff_eq] at hk
    exact ⟨⟨hlt, hk.1⟩, hk.2⟩
  · rw [hcnt]
    obtain rfl | rfl | rfl : c = 0 ∨ c = 1 ∨ c = 2 := by omega
    · rw [n1]; rfl
    · rw [n2]; rfl
    · rw [n3]; rfl

theorem uw7FLines_size : (uw7FLines ()).size = 15 := by
  unfold uw7FLines
  rw [flatMap_lines_eq lineOf fV fV (fun a b => a < b), List.size_toArray, List.length_map]
  decide

theorem uw7LLines_size : (uw7LLines ()).size = 30 := by
  have h := uw7Gens_size
  unfold uw7Gens at h
  rw [Array.size_append, uw7FLines_size] at h
  omega

theorem uw7LLines_get {g : ℕ} (hg : g < 30) : (uw7LLines ())[g]! = (uw7Gens ())[15 + g]! := by
  have hF := uw7FLines_size
  have hL := uw7LLines_size
  unfold uw7Gens
  rw [getElem!_pos (uw7LLines ()) g (by omega),
    getElem!_pos (uw7FLines () ++ uw7LLines ()) (15 + g) (by rw [Array.size_append]; omega),
    Array.getElem_append_right (by omega)]
  simp only [hF, Nat.add_sub_cancel_left]

variable (hL : ∀ u w, u < 4096 → w < 4096 → lineTree.memB (4096 * u + w) = true →
  lineIdx u w < 365211 ∧ linePair (lineIdx u w) = (u, w))

include hW hpb hpp hL in
theorem uw7ChkLevi_of_pinned : uw7ChkLevi () = true := by
  obtain ⟨h0l, h0⟩ := wt0
  obtain ⟨-, hEl, -⟩ := bE0_facts
  obtain ⟨hE, hEx⟩ := ubE0
  unfold uw7ChkLevi
  rw [uw7E0_eq hW hpb hpp]
  simp only [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true, decide_eq_true_eq]
  refine ⟨uw7LLines_size, fun g hg => ?_⟩
  have hg30 : g < 30 := by rw [uw7LLines_size] at hg; exact hg
  rw [← getElem!_pos (uw7LLines ()) g hg, uw7LLines_get hg30]
  have hg45 : 15 + g < 45 := by omega
  obtain ⟨-, -, -, -, -, h1⟩ := gen_facts hg45
  refine ⟨⟨(uw7Gens_line hL hg45).1, planeImg_gen hW hL hg45 h0l h0l (by rw [h0, exC_one, h1])⟩,
    planeImg_gen hW hL hg45 hEl hEl ?_⟩
  rw [← wt64_get hE, hEx]
  exact ubLevi g hg30

include hW hpb hpp hL in
theorem uw7B_of_pinned : ∀ v < 75735, uw7InB (uw7E0 ()) v = true → Relation.ReflTransGen
    (fun a b => ∃ g < 30, uw7InB (uw7E0 ()) a = true ∧ uw7InB (uw7E0 ()) b = true ∧
      uw7BCls (uw7E0 ()) a = uw7BCls (uw7E0 ()) b ∧ planeImg (uw7LLines ())[g]! a = b)
    ((uw7BReps ())[uw7BCls (uw7E0 ()) v - 1]!) v := by
  obtain ⟨-, hn, -, -⟩ := SmithD6Trees.wt_facts
  have hn64 := wt64_facts.2.1
  rw [uw7E0_eq hW hpb hpp]
  intro v hv hin
  have hv64 : v < J.wt64C.flatten.length := by rw [hn64]; exact hv
  have hk := (inB_iff hW hv).1 hin
  have hkv : uw7BCls JB.bE0 v = pkGet JB.bK 2 v := by rw [ubK_model hW hv, if_pos hin]
  have hc : uw7BCls JB.bE0 v - 1 < 3 := by
    have := uw7BCls_le JB.bE0 v
    have := uw7BCls_pos JB.bE0 v
    omega
  rw [uw7BReps_eq hW hpb hpp hc, Nat.sub_add_cancel (Nat.pos_of_ne_zero (uw7BCls_pos _ _)), hkv]
  have hR := ubReach v hv64 hk
  generalize hK : pkGet JB.bK 2 v = K at hk hR ⊢
  suffices H : ∀ b, Relation.ReflTransGen ubStep (ubRep K) b → b < 75735 → pkGet JB.bK 2 b = K →
      Relation.ReflTransGen (fun a b => ∃ g < 30, uw7InB JB.bE0 a = true ∧
        uw7InB JB.bE0 b = true ∧ uw7BCls JB.bE0 a = uw7BCls JB.bE0 b ∧
          planeImg (uw7LLines ())[g]! a = b) (ubRep K) b from H v hR hv hK
  intro b hb
  induction hb with
  | refl => exact fun _ _ => Relation.ReflTransGen.refl
  | @tail a b _ hab ih =>
    intro hb hbK
    have hab' : ∃ g < 30, pkGet JB.bK 2 a = pkGet JB.bK 2 b ∧
        ∃ (ha : a < J.wt64C.flatten.length) (hb : b < J.wt64C.flatten.length),
          liftT (JU.uwT.getD (15 + g) []) (J.wt64C.flatten[a]'ha) = J.wt64C.flatten[b]'hb := hab
    obtain ⟨g, hg, hkab, ha, hb64, hl⟩ := hab'
    have ha' : a < 75735 := by rw [← hn64]; exact ha
    have haK : pkGet JB.bK 2 a = K := hkab.trans hbK
    refine Relation.ReflTransGen.tail (ih ha' haK) ⟨g, hg, (inB_iff hW ha').2 (by omega),
      (inB_iff hW hb).2 (by omega), ?_, ?_⟩
    · rw [ubK_model hW ha', ubK_model hW hb] at hkab
      rw [if_pos ((inB_iff hW ha').2 (by omega)), if_pos ((inB_iff hW hb).2 (by omega))] at hkab
      exact hkab
    · have ha32 : a < J.wtC.flatten.length := by rw [hn]; exact ha'
      have hb32 : b < J.wtC.flatten.length := by rw [hn]; exact hb
      rw [wt64_get ha, wt64_get hb64] at hl
      rw [uw7LLines_get hg]
      exact planeImg_gen hW hL (by omega) ha32 hb32 hl

include hW hpb hpp hL in
theorem uw7Wit_of_pinned : ∀ v < 75735, uw7InB (uw7E0 ()) v = true → uw7BCls (uw7E0 ()) v = 1 →
    ∃ k < 365211, (linePair k).1 &&& 63 = 0 ∧ (linePair k).2 &&& 63 = 0 ∧
      planeImgM (tvCols k) (uw7E0 ()) = v := by
  obtain ⟨-, hn, -, -⟩ := SmithD6Trees.wt_facts
  have hn64 := wt64_facts.2.1
  obtain ⟨-, hEl, -⟩ := bE0_facts
  obtain ⟨hE, hEx⟩ := ubE0
  rw [uw7E0_eq hW hpb hpp]
  intro v hv hin hc
  have hv64 : v < J.wt64C.flatten.length := by rw [hn64]; exact hv
  have hv32 : v < J.wtC.flatten.length := by rw [hn]; exact hv
  have hk1 : pkGet JB.bK 2 v = 1 := by rw [ubK_model hW hv, if_pos hin, hc]
  obtain ⟨K, hmem, h1, h2, h3, hu, hw, hrho⟩ := ubWit v hv64 hk1
  have hK : 4096 * (K / 4096) + K % 4096 = K := Nat.div_add_mod K 4096
  obtain ⟨hlt, hpair⟩ := hL (K / 4096) (K % 4096) (by omega) (by omega) (by rw [hK]; exact hmem)
  refine ⟨lineIdx (K / 4096) (K % 4096), hlt, by rw [hpair]; exact hu, by rw [hpair]; exact hw, ?_⟩
  unfold planeImgM
  have hwE : wtArr[JB.bE0]! = J.wtC.flatten[JB.bE0]'hEl := wt_eq hW hEl
  rw [hwE, applyCols_of_rho hpair (wtC_lt hv32) ?_, wtIdx_get hW hv32]
  rw [← wt64_get hE, hEx, ← wt64_get hv64, ← hrho, rhoK_eq, rhoK_eq]

end Model

end CertificateChecks.SmithD6UwB

end
