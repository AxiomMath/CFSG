module

public import Certificates.Kernel.SmithD6Adj.Checks
public import Certificates.Kernel.SmithD6Wt.Math
public import Certificates.Kernel.SmithD6Stab.Glue
public import CFSG.Certificates.Kernel.SmithD6AdjSound

set_option maxRecDepth 100000

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CertificateChecks.SmithD6Adj

open CFSG.SmithD6 CFSG.KC.KeyTree CFSG.KD.SmithD6 CFSG.KD.SmithD6Adj
  CFSG.GF2Type.SmithTypeE.DMod CertificateChecks.SmithD6Wt CertificateChecks.SmithD6Stab

theorem d6a_mf7Any_iff (n : Nat) (p : Nat → Bool) :
    mf7Any n p = true ↔ ∃ i < n, p i = true := by
  have : mf7Any n p = (List.range' 0 n).any p := by
    unfold mf7Any
    simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
    simp only [d6s_forIn_flag, pure_bind]
    by_cases hA : (List.range' 0 n).any p = true
    · simp [hA] <;> rfl
    · simp [hA] <;> rfl
  rw [this]
  simp [List.any_eq_true, List.mem_range'_1]

theorem gensT_length : JT.gensT.length = 13 := by decide +kernel

theorem adj_all : ∀ x ∈ J.wt64C.flatten, adjOK x = true := by
  intro x hx
  obtain ⟨l, hl, hx⟩ := List.mem_flatten.1 hx
  obtain ⟨c, hc, rfl⟩ := List.getElem_of_mem hl
  have h := adjChunks_ok c (by rw [wt64C_length] at hc; exact hc)
  rw [d6AdjOK, nthC_eq, getD_eq hc] at h
  exact adjGo_sound _ h x hx

theorem memB_of_mem {t : Nat} (h : t ∈ J.wtC.flatten) : wtTree.memB t = true := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem h
  have := SmithD6Trees.wt_facts.2.2.1 i hi
  simp only [KT.memB, this]
  rfl

theorem mem_of_memB64 {y : Nat} (h : wt64Tree.memB y = true) :
    ∃ t ∈ J.wtC.flatten, exC t = y := by
  have hpos : 0 < wt64Tree.find y := Nat.le_of_ble_eq_true h
  obtain ⟨v, hvdef⟩ : ∃ v, v = wt64Tree.find y - 1 := ⟨_, rfl⟩
  obtain ⟨hv, hx⟩ := wt64_facts.2.2.2 y v (by omega)
  have hv' : v < J.wtC.flatten.length := by
    rw [wtC_flatten_length]
    rw [wt64_facts.2.1] at hv
    exact hv
  refine ⟨J.wtC.flatten[v]'hv', List.getElem_mem hv', ?_⟩
  have e : J.wt64C.flatten[v]'hv = exC (J.wtC.flatten[v]'hv') := by
    rw [List.getElem_of_eq wt64_eq_map.1 hv, List.getElem_map]
  rw [← e, hx]

theorem d6a_tvCols_lt (k : ℕ) {c : ℕ} (hc : c < 32) : (tvCols k)[c]! < 2 ^ 32 := by
  unfold tvCols
  simp only
  rw [getElem!_pos _ c (by simp [hc])]
  simp only [Array.getElem_ofFn]
  exact Nat.xor_lt_two_pow (Nat.and_lt_two_pow _ (by norm_num))
    (Nat.pow_lt_pow_right (by norm_num) hc)

theorem d6a_applyCols_lt {cols : Array ℕ} (hsz : cols.size = 32)
    (h : ∀ c < 32, cols[c]! < 2 ^ 32) (y : ℕ) : applyCols cols y < 2 ^ 32 := by
  unfold applyCols
  rw [hsz]
  have key : ∀ n ≤ 32, (List.range n).foldl
      (fun acc m => if y.testBit m then acc ^^^ cols[m]! else acc) 0 < 2 ^ 32 := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      split_ifs
      · exact Nat.xor_lt_two_pow (ih (by omega)) (h n (by omega))
      · exact ih (by omega)
  exact key 32 le_rfl

theorem lt_of_mem {t : Nat} (h : t ∈ J.wtC.flatten) : t < 2 ^ 32 := wt64_eq_map.2 t h

theorem ne_zero_of_mem {t : Nat} (h : t ∈ J.wtC.flatten) : t ≠ 0 := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem h
  have h0 := first.1
  have hl : 0 < J.wtC.flatten.length := by omega
  rw [List.getD_eq_getElem _ _ hl] at h0
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · omega
  · have := List.pairwise_iff_getElem.1 SmithD6Trees.wt_facts.1 0 i hl hi hpos
    omega

theorem eq_of_exL {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32)
    (h : exL (decode32 a) = exL (decode32 b)) : a = b :=
  eq_of_decode32_eq ha hb (exL_injective h)

theorem rhoT_eq_xor (ts : List (Nat × Nat × Bool)) (x : Nat) : rhoT ts x = x ^^^ liftT ts x := by
  rw [liftT, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]

theorem lift_facts {s : Nat} (hs : s ∈ J.wtC.flatten) {g : Nat} (hg : g < 13) :
    ∃ t ∈ J.wtC.flatten, exC t = liftT (JT.gensT.getD g []) (exC s) ∧
      (rhoT (JT.gensT.getD g []) (exC s) = 0 → t = s) ∧
      (wt64Tree.memB (rhoT (JT.gensT.getD g []) (exC s)) = true →
        t ≠ s ∧ (s ^^^ t) ∈ J.wtC.flatten) := by
  have hs64 : exC s ∈ J.wt64C.flatten := by
    rw [wt64_eq_map.1]
    exact List.mem_map_of_mem hs
  obtain ⟨t, ht, hte⟩ := mem_of_memB64 (closure (exC s) hs64 g hg)
  refine ⟨t, ht, hte, fun h0 => ?_, fun hm => ?_⟩
  · rw [liftT, h0, Nat.xor_zero] at hte
    refine eq_of_exL (lt_of_mem ht) (lt_of_mem hs) ?_
    rw [← decode64_exC, ← decode64_exC, hte]
  · obtain ⟨t3, ht3, he3⟩ := mem_of_memB64 hm
    have hx : t3 = s ^^^ t := by
      refine eq_of_exL (lt_of_mem ht3) (Nat.xor_lt_two_pow (lt_of_mem hs) (lt_of_mem ht)) ?_
      rw [← decode64_exC, he3, rhoT_eq_xor, decode64_xor, ← hte, decode64_exC, decode64_exC,
        exL_decode32_xor]
    refine ⟨fun hts => ne_zero_of_mem ht3 ?_, hx ▸ ht3⟩
    rw [hx, hts, Nat.xor_self]

section Model

variable (hwt : ∀ j (hj : j < J.wtC.flatten.length), wt j = J.wtC.flatten[j])
  (hidx : ∀ x, wtIdx x < 75735 ↔ wtTree.memB x = true)
include hwt hidx

theorem wtIdx_of_mem {t : Nat} (ht : t ∈ J.wtC.flatten) :
    wtIdx t < 75735 ∧ wt (wtIdx t) = t := by
  have h := (hidx t).2 (memB_of_mem ht)
  exact ⟨h, mf7_wt_wtIdx t h⟩

theorem wt_mem {i : Nat} (hi : i < 75735) : wt i ∈ J.wtC.flatten := by
  have hi' : i < J.wtC.flatten.length := by rw [wtC_flatten_length]; exact hi
  rw [hwt i hi']
  exact List.getElem_mem hi'

theorem wt_inj {a b : Nat} (ha : a < 75735) (hb : b < 75735) (h : wt a = wt b) : a = b := by
  have ha' : a < J.wtC.flatten.length := by rw [wtC_flatten_length]; exact ha
  have hb' : b < J.wtC.flatten.length := by rw [wtC_flatten_length]; exact hb
  rw [hwt a ha', hwt b hb'] at h
  have hp := SmithD6Trees.wt_facts.1
  rcases Nat.lt_trichotomy a b with hab | hab | hab
  · have := List.pairwise_iff_getElem.1 hp a b ha' hb' hab
    omega
  · exact hab
  · have := List.pairwise_iff_getElem.1 hp b a hb' ha' hab
    omega

theorem adjW_of_mem {i j : Nat} (h : (wt i ^^^ wt j) ∈ J.wtC.flatten) : adjW i j = true := by
  unfold adjW
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  exact Or.inr (wtIdx_of_mem hwt hidx h).1

theorem mf7ChkWt_of_pinned : mf7ChkWt () = true := by
  unfold mf7ChkWt
  simp only [Bool.and_eq_true, d6s_mf7All_iff, beq_iff_eq, bne_iff_ne, decide_eq_true_eq]
  refine ⟨⟨fun j hj => ?_, fun i hi => ⟨ne_zero_of_mem (wt_mem hwt hidx hi), ?_⟩⟩, fun i hi => ?_⟩
  · obtain ⟨h1, h2⟩ := wtIdx_of_mem hwt hidx (wt_mem hwt hidx hj)
    exact wt_inj hwt hidx h1 hj h2
  · exact lt_of_mem (wt_mem hwt hidx hi)
  · rw [d6a_mf7Any_iff]
    have hs := wt_mem hwt hidx hi
    have hs64 : exC (wt i) ∈ J.wt64C.flatten := by
      rw [wt64_eq_map.1]
      exact List.mem_map_of_mem hs
    obtain ⟨h1, h2⟩ := adjOK_sound (adj_all _ hs64)
    obtain ⟨g, hg, hr, hm⟩ : ∃ g < 13, rhoT (JT.gensT.getD g []) (exC (wt i)) ≠ 0 ∧
        wt64Tree.memB (rhoT (JT.gensT.getD g []) (exC (wt i))) = true := by
      by_cases h0 : rhoT (JT.gensT.getD 0 []) (exC (wt i)) = 0
      · obtain ⟨ts, hts, hr, hm⟩ := h2 h0
        obtain ⟨g, hg, rfl⟩ := List.getElem_of_mem hts
        refine ⟨g, by rw [gensT_length] at hg; exact hg, ?_⟩
        rw [List.getD_eq_getElem _ _ hg]
        exact ⟨hr, hm⟩
      · exact ⟨0, by decide, h0, h1.resolve_left h0⟩
    obtain ⟨t, ht, -, -, h3⟩ := lift_facts hs hg
    obtain ⟨hne, hsum⟩ := h3 hm
    obtain ⟨hj, hwj⟩ := wtIdx_of_mem hwt hidx ht
    refine ⟨wtIdx t, hj, ?_⟩
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq]
    refine ⟨adjW_of_mem hwt hidx (by rw [hwj]; exact hsum), ?_⟩
    rw [hwj]
    exact hne

theorem mf7ChkTvAdj0_of_pinned (hK : lineKeys.toList = J.lineKeysC.flatten) :
    mf7ChkTvAdj0 () = true := by
  have hp0 : linePair 0 = (1, 2) := by rw [linePair_eq hK, key_zero]; rfl
  unfold mf7ChkTvAdj0
  simp only [d6s_mf7All_iff]
  intro i hi
  have hs := wt_mem hwt hidx hi
  obtain ⟨t, ht, hte, h0, hm⟩ := lift_facts hs (g := 0) (by decide)
  have hv : mf7Ap (tvCols 0) (wt i) = t := by
    rw [mf7Ap_eq]
    have hsz : (tvCols 0).size = 32 := by simp [tvCols]
    refine eq_of_exL (d6a_applyCols_lt hsz (fun c hc => d6a_tvCols_lt 0 hc) _) (lt_of_mem ht) ?_
    rw [decode32_applyCols hsz, exL_colsLin_tvCols, hp0, ← decode64_exC t, hte,
      decode64_liftT (gensT_ok 0 (by decide)) (exC_lt_two_pow _), decode64_exC]
    rfl
  rw [hv]
  obtain ⟨hj, hwj⟩ := wtIdx_of_mem hwt hidx ht
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  refine ⟨⟨hj, hwj⟩, ?_⟩
  obtain ⟨h1, -⟩ := adjOK_sound (adj_all _ (by rw [wt64_eq_map.1]; exact List.mem_map_of_mem hs))
  rcases h1 with h1 | h1
  · unfold adjW
    rw [hwj, h0 h1]
    simp
  · exact adjW_of_mem hwt hidx (by rw [hwj]; exact (hm h1).2)

end Model

end CertificateChecks.SmithD6Adj

end
