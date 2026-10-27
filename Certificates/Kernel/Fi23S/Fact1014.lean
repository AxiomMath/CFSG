
module

public import Certificates.Kernel.Fi23S.Fact1013
public import Certificates.Kernel.Fi23S.Cyc
public import Certificates.Kernel.Fi23R.Fact2074
import Certificates.Kernel.Fi23S.Small
import Certificates.Kernel.Fi23S.L14a
import Certificates.Kernel.Fi23S.L14b
import Certificates.Kernel.Fi23S.L14c
import Certificates.Kernel.Fi23S.L14d
import Certificates.Kernel.Fi23R.Uniq
import Certificates.Kernel.Sporadic.ON.Gen
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import Mathlib
public import CFSG.Sporadic.Fi23.InvCertBase
public import CFSG.Sporadic.Fi23.InvCoverBase

public section

set_option maxRecDepth 400000

#kon_join CFSG.KD.Fi23S.l14All CFSG.KD.Fi23S.l14F 11

namespace CertificateChecks.KernelFi23S

open CFSG.KC.Enum CFSG.KC.Fi23K CFSG.KC.Fi23R CFSG.KC.Fi23S CFSG.KD.Fi23K CFSG.KD.Fi23S
  CFSG.KD.Fi23R CFSG.KS.Raw.Orb CFSG.KS.TBfs CFSG.KS.PC CFSG.KS.PEnum CFSG.Sporadic.Fi23.Native
  CFSG.Sporadic.Th.Native CFSG.Perm.Native CertificateChecks.KernelFi23R
  CertificateChecks.KernelFi23M

theorem misc_facts : tb G 43 39 = 39 ∧ tA G 1 39 = 39 ∧
    cntS (fxW G [43]) 0 31671 = 3511 ∧ cntS (fun x => Nat.beq (tb H 42 x) x) 0 31671 = 695 ∧
    cntS (fun x => Nat.beq (tb H 43 x) x) 0 31671 = 183 ∧ tb H 43 2 ≠ 2 := by
  have h := miscS_ok
  unfold miscS at h
  rw [bAnd_eq, bAnd_eq, bAnd_eq, bAnd_eq, bAnd_eq] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2, Nat.eq_of_beq_eq_true h3,
    Nat.eq_of_beq_eq_true h4, Nat.eq_of_beq_eq_true h5, fun e => ?_⟩
  rw [e] at h6
  exact absurd h6 (by decide)

theorem l14B_cover : ∀ k < 512, ∃ s < 11, List.getD l14B s 0 ≤ k ∧
    k < List.getD l14B (s + 1) 0 := by
  decide

theorem lf14_all {k j : Nat} (hk : k < 512) (hj : j < 512) : lf14 k j = true := by
  have hb : ∀ s < 11, List.getD l14B s 0 ≤ k → k < List.getD l14B (s + 1) 0 →
      lf14 k j = true := by
    intro s hs h1 h2
    have h := l14All s hs
    unfold l14F at h
    rw [strictB_eq] at h
    unfold l14Sl at h
    have h' := allN_iff.1 h (k - List.getD l14B s 0) (by
      change k - List.getD l14B s 0 < List.getD l14B (s + 1) 0 - List.getD l14B s 0
      omega)
    rw [strictB_eq] at h'
    have e : Nat.add (List.getD l14B s 0) (k - List.getD l14B s 0) = k := by
      change List.getD l14B s 0 + (k - List.getD l14B s 0) = k
      omega
    rw [e] at h'
    exact allN_iff.1 h' j hj
  obtain ⟨s, hs, h1, h2⟩ := l14B_cover k hk
  exact hb s hs h1 h2

theorem lf14_cases {k j : Nat} (h : lf14 k j = true) (hc : 2 ≤ code k j) :
    (code k j - 2) / 4 < 29 ∧ ∀ q < 6,
      cyK (hK k j ((code k j - 2) / 4)) q 119 1 (hK k j ((code k j - 2) / 4) q) % 2 = 1 := by
  have h2 : ¬ code k j < 2 := by omega
  unfold lf14 lf14c at h
  rw [strictB_eq, bIf_eq, if_neg (by rw [Nat.blt_eq]; exact h2), strictB_eq, bAnd_eq,
    Bool.and_eq_true] at h
  have e : Nat.shiftRight (Nat.sub (code k j) 2) 2 = (code k j - 2) / 4 := by
    change (code k j - 2) >>> 2 = _
    rw [Nat.shiftRight_eq_div_pow]
  rw [e] at h
  refine ⟨Nat.blt_eq.mp h.1, fun q hq => ?_⟩
  have h2 := allN_iff.1 h.2 q hq
  rw [strictB_eq] at h2
  have h3 := Nat.eq_of_beq_eq_true h2
  change _ &&& 1 = 1 at h3
  rw [Nat.and_one_is_mod] at h3
  exact h3

theorem wordsABC_ok : (∀ i < 17, ∀ z ∈ wordsC[i]!, z = 1 ∨ z = -1 ∨ z = 2 ∨ z = -2) ∧
    (∀ i < 10, ∀ z ∈ wordsB[i]!, z = 1 ∨ z = -1 ∨ z = 2 ∨ z = -2) ∧
    (∀ i < 2, ∀ z ∈ wordsA[i]!, z = 1 ∨ z = -1 ∨ z = 2 ∨ z = -2) := by
  decide

theorem UR_eq : (∀ i < 17, UR.getD i [] = (wordsC[i]!).reverse.map regZ ∧
      URi.getD i [] = invW ((wordsC[i]!).reverse.map regZ)) ∧
    (∀ i < 10, UR.getD (17 + i) [] = (wordsB[i]!).reverse.map regZ ∧
      URi.getD (17 + i) [] = invW ((wordsB[i]!).reverse.map regZ)) ∧
    (∀ i < 2, UR.getD (27 + i) [] = (wordsA[i]!).reverse.map regZ ∧
      URi.getD (27 + i) [] = invW ((wordsA[i]!).reverse.map regZ)) := by
  decide +kernel

theorem conjsOf_size (X : Table) (ws : Array (List Int)) : (conjsOf orbLit X ws).size = ws.size := by
  unfold conjsOf
  rw [Array.size_map]

theorem conjsOf_get (X : Table) (ws : Array (List Int)) {i : Nat} (hi : i < ws.size) :
    (conjsOf orbLit X ws)[i]! = (wordT 31671 (genTables orbLit) ws[i]!,
      invT 31671 (wordT 31671 (genTables orbLit) ws[i]!),
      compT 31671 (wordT 31671 (genTables orbLit) ws[i]!)
        (compT 31671 X (invT 31671 (wordT 31671 (genTables orbLit) ws[i]!)))) := by
  unfold conjsOf
  rw [getElem!_pos _ i (by rw [Array.size_map]; exact hi), Array.getElem_map, getElem!_pos _ i hi]

theorem invOK_all (X : Table) (ws : Array (List Int))
    (hw : ∀ i < ws.size, ∀ z ∈ ws[i]!, z = 1 ∨ z = -1 ∨ z = 2 ∨ z = -2) :
    (conjsOf orbLit X ws).all (fun W => invOK 31671 W.1 W.2.1) = true := by
  rw [Array.all_eq_true]
  intro i hi
  rw [conjsOf_size] at hi
  rw [← getElem!_pos _ i (by rw [conjsOf_size]; exact hi), conjsOf_get X ws hi]
  exact rw_invOK dP_sq (rw_wordT _ (hw i hi))

theorem conj_ap {X : Table} {f : Nat → Nat} (hX : ∀ y < 31671, ap X y = f y ∧ f y < 31671)
    (ws : Array (List Int)) {i : Nat} (hi : i < ws.size)
    (hw : ∀ z ∈ ws[i]!, z = 1 ∨ z = -1 ∨ z = 2 ∨ z = -2) {y : Nat} (hy : y < 31671) :
    ap (conjsOf orbLit X ws)[i]!.2.2 y =
      wa G ((ws[i]!).reverse.map regZ) (f (wa G (invW ((ws[i]!).reverse.map regZ)) y)) ∧
    wa G ((ws[i]!).reverse.map regZ) (f (wa G (invW ((ws[i]!).reverse.map regZ)) y)) < 31671 := by
  have hW := rw_wordT _ hw
  have hWi := rw_invT dP_sq hW
  obtain ⟨a1, l1⟩ := hWi.tr.2 y hy
  obtain ⟨a2, l2⟩ := hX _ l1
  obtain ⟨a3, l3⟩ := hW.tr.2 _ l2
  rw [conjsOf_get X ws hi]
  refine ⟨?_, l3⟩
  simp only
  rw [ap_comp hy, ap_comp hy, a1, a2, a3]

theorem xEv_C {r y : Nat} (hr : r < 17) : xEv r y = tb H 43 y := by
  unfold xEv
  rw [nIf_eq, if_pos (Nat.blt_eq.mpr hr)]

theorem xEv_B {r y : Nat} (h1 : 17 ≤ r) (hr : r < 27) : xEv r y = tb H 42 y := by
  have h2 : ¬ r < 17 := by omega
  unfold xEv
  rw [nIf_eq, if_neg (by rw [Nat.blt_eq]; exact h2), nIf_eq, if_pos (Nat.blt_eq.mpr hr)]

theorem xEv_A {r y : Nat} (h1 : 27 ≤ r) : xEv r y = tb G 43 y := by
  have h2 : ¬ r < 17 := by omega
  have h3 : ¬ r < 27 := by omega
  unfold xEv
  rw [nIf_eq, if_neg (by rw [Nat.blt_eq]; exact h2), nIf_eq, if_neg (by rw [Nat.blt_eq]; exact h3)]

theorem D_ap {y : Nat} (hy : y < 31671) : ap (dTab orbLit) y = tb G 43 y ∧ tb G 43 y < 31671 := by
  refine ⟨?_, rng 43 (by norm_num) y hy⟩
  rw [rw_dTab.ap hy, wa_cons, wa_nil, lf_eq, if_pos (by norm_num)]

theorem XB_ap {y : Nat} (hy : y < 31671) :
    ap (compT 31671 (dTab orbLit) (treeActTab orbLit (dTab orbLit) (genTables orbLit (-2)) 1)) y =
      tb H 42 y ∧ tb H 42 y < 31671 := by
  have e : ap (compT 31671 (dTab orbLit)
      (treeActTab orbLit (dTab orbLit) (genTables orbLit (-2)) 1)) y = tb H 42 y := by
    rw [rw_X.ap hy, xb_pt hy]
    have e1 : wX = [129, 43] := rfl
    rw [e1, wa_cons, wa_cons, wa_nil, lf_eq, lf_eq, if_pos (by norm_num : (43 : Nat) < 128),
      if_neg (by norm_num : ¬ (129 : Nat) < 128)]
  refine ⟨e, ?_⟩
  rw [xb_pt hy]
  exact rng 43 (by norm_num) _ (tA_lt 1 hy)

theorem XC_ap {y : Nat} (hy : y < 31671) :
    ap (compT 31671 (compT 31671 (dTab orbLit)
      (treeActTab orbLit (dTab orbLit) (genTables orbLit (-2)) 1))
      (treeActTab orbLit (dTab orbLit) (genTables orbLit (-2)) 39)) y =
      tb H 43 y ∧ tb H 43 y < 31671 := by
  have e : ap (compT 31671 (compT 31671 (dTab orbLit)
      (treeActTab orbLit (dTab orbLit) (genTables orbLit (-2)) 1))
      (treeActTab orbLit (dTab orbLit) (genTables orbLit (-2)) 39)) y = tb H 43 y := by
    rw [rw_XC.ap hy, xc_pt hy, xb_pt (tA_lt 39 hy)]
    have e1 : wXC = [167, 129, 43] := rfl
    rw [e1, wa_cons, wa_cons, wa_cons, wa_nil, lf_eq, lf_eq, lf_eq,
      if_pos (by norm_num : (43 : Nat) < 128), if_neg (by norm_num : ¬ (129 : Nat) < 128),
      if_neg (by norm_num : ¬ (167 : Nat) < 128)]
  refine ⟨e, ?_⟩
  rw [xc_pt hy, xb_pt (tA_lt 39 hy)]
  exact rng 43 (by norm_num) _ (tA_lt 1 (tA_lt 39 hy))

theorem cyK_congr {h h' : Nat → Nat} (hh : ∀ y < 31671, h y = h' y)
    (hr : ∀ y < 31671, h' y < 31671) (q : Nat) :
    ∀ f l x, x < 31671 → cyK h q f l x = cyK h' q f l x
  | 0, l, x, _ => by rw [cyK_zero, cyK_zero]
  | f + 1, l, x, hx => by
    rw [cyK_succ, cyK_succ, hh x hx, cyK_congr hh hr q f (l + 1) (h' x) (hr x hx)]

theorem rep_odd {k j r : Nat} (hk : k < 512) (hj : j < 512) {X : Table} {ws : Array (List Int)}
    {i : Nat} (hi : i < ws.size) (hw : ∀ z ∈ ws[i]!, z = 1 ∨ z = -1 ∨ z = 2 ∨ z = -2)
    (hX : ∀ y < 31671, ap X y = xEv r y ∧ xEv r y < 31671)
    (hu : UR.getD r [] = (ws[i]!).reverse.map regZ ∧
      URi.getD r [] = invW ((ws[i]!).reverse.map regZ))
    (hcyc : ∀ q < 6, cyK (hK k j r) q 119 1 (hK k j r q) % 2 = 1) :
    oddOK (compT 31671 t0[k]! t1[j]!) (conjsOf orbLit X ws)[i]!.2.2 = true := by
  have hR : ∀ y < 31671, ap (conjsOf orbLit X ws)[i]!.2.2 y = rEv r y ∧ rEv r y < 31671 := by
    intro y hy
    have e : rEv r y = wa G ((ws[i]!).reverse.map regZ)
        (xEv r (wa G (invW ((ws[i]!).reverse.map regZ)) y)) := by
      unfold rEv
      rw [hu.1, hu.2]
    rw [e]
    exact conj_ap hX ws hi hw hy
  have hPR : ∀ y < 31671, ap (compT 31671 t0[k]! t1[j]!) (ap (conjsOf orbLit X ws)[i]!.2.2 y) =
      hK k j r y := fun y hy => by
    rw [(hR y hy).1, leaf_ap hk hj (hR y hy).2]
    rfl
  have hlt : ∀ y < 31671, hK k j r y < 31671 := fun y hy => gK_lt hk hj (hR y hy).2
  apply oddOK_of
  intro q hq
  have hq' : q < 31671 := by omega
  rw [hPR q hq', cyK_congr hPR hlt q 119 1 _ (hlt q hq')]
  exact hcyc q hq

noncomputable abbrev XBt : Table :=
  compT 31671 (dTab orbLit) (treeActTab orbLit (dTab orbLit) (genTables orbLit (-2)) 1)
noncomputable abbrev XCt : Table :=
  compT 31671 XBt (treeActTab orbLit (dTab orbLit) (genTables orbLit (-2)) 39)

theorem noninv_ok {k j : Nat} (hk : k < 512) (hj : j < 512) {b : Nat} (hb : b < 6)
    (hne : gK k j (gK k j b) ≠ b) : invo2OK 31671 t0[k]! t1[j]! = false := by
  rw [Bool.eq_false_iff]
  intro h
  unfold invo2OK at h
  rw [CFSG.KS.TW.allIn_iff] at h
  have hb' : b < 31671 := by omega
  have h' := h b hb'
  rw [beq_iff_eq, leaf_ap2 hk hj (y := b) hb', leaf_ap2 hk hj (y := gK k j b) (gK_lt hk hj hb')] at h'
  exact hne h'

theorem id_ok {k j : Nat} (hk : k < 512) (hj : j < 512) (hfix : ∀ b < 6, gK k j b = b) :
    CFSG.Sporadic.Fi23.Native.isIdT (compT 31671 t0[k]! t1[j]!) = true := by
  have hg := one_of_fix (leaf_mem hk hj) fun b hb => by rw [← gK_eq hk hj (by omega)]; exact hfix b hb
  exact isIdT_of fun i hi => by rw [leaf_ap hk hj hi, gK_eq hk hj hi, hg, actN_one]

theorem leaf14 {k j : Nat} (hk : k < 512) (hj : j < 512) :
    coverPair (conjsOf orbLit (dTab orbLit) wordsA) (conjsOf orbLit XBt wordsB)
      (conjsOf orbLit XCt wordsC) t0[k]! t1[j]! = true := by
  unfold coverPair
  rcases lf13_cases (lf13_all hk hj) with ⟨-, b, hb, hne⟩ | ⟨-, hfix⟩ | ⟨hc2, -⟩ | ⟨hc2, -⟩
  · rw [noninv_ok hk hj hb hne]
    rfl
  · have hl : coverLeaf (conjsOf orbLit (dTab orbLit) wordsA) (conjsOf orbLit XBt wordsB)
        (conjsOf orbLit XCt wordsC) (compT 31671 t0[k]! t1[j]!) = true := by
      unfold coverLeaf
      rw [id_ok hk hj hfix]
      rfl
    rw [hl, Bool.or_true]
  all_goals
    obtain ⟨hr, hcyc⟩ := lf14_cases (lf14_all hk hj) hc2
    obtain ⟨uC, uB, uA⟩ := UR_eq
    obtain ⟨wC, wB, wA⟩ := wordsABC_ok
    have hl : coverLeaf (conjsOf orbLit (dTab orbLit) wordsA) (conjsOf orbLit XBt wordsB)
        (conjsOf orbLit XCt wordsC) (compT 31671 t0[k]! t1[j]!) = true := by
      unfold coverLeaf
      rcases (by omega : (code k j - 2) / 4 < 17 ∨ (17 ≤ (code k j - 2) / 4 ∧
          (code k j - 2) / 4 < 27) ∨ 27 ≤ (code k j - 2) / 4) with h | h | h
      · have ho := rep_odd (X := XCt) (ws := wordsC) (i := (code k j - 2) / 4) hk hj h (wC _ h)
          (fun y hy => by rw [xEv_C h]; exact XC_ap hy) (uC _ h) hcyc
        have ha : (conjsOf orbLit XCt wordsC).any (fun W => oddOK (compT 31671 t0[k]! t1[j]!)
            W.2.2) = true := by
          rw [Array.any_eq_true]
          refine ⟨(code k j - 2) / 4, by rw [conjsOf_size]; exact h, ?_⟩
          rw [← getElem!_pos _ _ (by rw [conjsOf_size]; exact h)]
          exact ho
        rw [ha]
        simp
      · have e : (code k j - 2) / 4 = 17 + ((code k j - 2) / 4 - 17) := by omega
        have hi : (code k j - 2) / 4 - 17 < 10 := by omega
        have hu := uB _ hi
        rw [← e] at hu
        have ho := rep_odd (X := XBt) (ws := wordsB) (i := (code k j - 2) / 4 - 17) hk hj hi
          (wB _ hi) (fun y hy => by rw [xEv_B h.1 h.2]; exact XB_ap hy) hu hcyc
        have ha : (conjsOf orbLit XBt wordsB).any (fun W => oddOK (compT 31671 t0[k]! t1[j]!)
            W.2.2) = true := by
          rw [Array.any_eq_true]
          refine ⟨(code k j - 2) / 4 - 17, by rw [conjsOf_size]; exact hi, ?_⟩
          rw [← getElem!_pos _ _ (by rw [conjsOf_size]; exact hi)]
          exact ho
        rw [ha]
        simp
      · have e : (code k j - 2) / 4 = 27 + ((code k j - 2) / 4 - 27) := by omega
        have hi : (code k j - 2) / 4 - 27 < 2 := by omega
        have hu := uA _ hi
        rw [← e] at hu
        have ho := rep_odd (X := dTab orbLit) (ws := wordsA) (i := (code k j - 2) / 4 - 27) hk hj
          hi (wA _ hi) (fun y hy => by rw [xEv_A h]; exact D_ap hy) hu hcyc
        have ha : (conjsOf orbLit (dTab orbLit) wordsA).any
            (fun W => oddOK (compT 31671 t0[k]! t1[j]!) W.2.2) = true := by
          rw [Array.any_eq_true]
          refine ⟨(code k j - 2) / 4 - 27, by rw [conjsOf_size]; exact hi, ?_⟩
          rw [← getElem!_pos _ _ (by rw [conjsOf_size]; exact hi)]
          exact ho
        rw [ha]
        simp
    rw [hl, Bool.or_true]

theorem counts_ok : fixCount (dTab orbLit) = 3511 ∧ fixCount XBt = 695 ∧ fixCount XCt = 183 := by
  obtain ⟨-, -, h3, h4, h5, -⟩ := misc_facts
  refine ⟨?_, ?_, ?_⟩
  · unfold fixCount
    rw [rw_dTab.countP, ← cntS_zero]
    exact h3
  · unfold fixCount
    rw [← h4, cntS_zero]
    exact List.countP_congr fun i hi => by
      rw [beq_iff_eq, Nat.beq_eq, (XB_ap (List.mem_range.1 hi)).1]
  · unfold fixCount
    rw [← h5, cntS_zero]
    exact List.countP_congr fun i hi => by
      rw [beq_iff_eq, Nat.beq_eq, (XC_ap (List.mem_range.1 hi)).1]

theorem allk_ok : allIn 0 31671 (fun k => k == 0 || k == 1 || ap (dTab orbLit) k != k ||
    ap (treeActTab orbLit (dTab orbLit) (genTables orbLit (-2)) 1) k != k ||
    fixCount (compT 31671 XBt (treeActTab orbLit (dTab orbLit) (genTables orbLit (-2)) k)) ==
      183) = true := by
  obtain ⟨-, -, -, -, -, -, -, h8, -⟩ := base_facts
  have c39 : (List.range 31671).countP (fxW G (wX ++ [167])) = 183 := by
    have ha := uniq0_ok
    have hb := uniq1_ok
    unfold uniq0 uCnt at ha
    unfold uniq1 uCnt at hb
    replace ha := Nat.eq_of_beq_eq_true ha
    replace hb := Nat.eq_of_beq_eq_true hb
    have s := cntS_add (fxW G (wX ++ [167])) 0 23684 7987
    simp only [Nat.zero_add, Nat.reduceAdd] at s
    rw [← cntS_zero]
    omega
  have hr : nfix (cT 39 * wp wX) = 183 := by
    have e : wp (wX ++ [167]) = cT 39 * wp wX := by
      rw [wp_append, wp_cons, wp_nil, one_mul, lp_big (by norm_num)] <;> rfl
    rw [← e, ← countP_nfix _ (ok_append ok_wX (by decide)), c39]
  have hs : orbSl G wX exU (wr 0) gU 39 39 0 31671 = true := uscan_ok
  rw [CFSG.KS.TW.allIn_iff]
  intro k hk
  by_cases h0 : k = 0
  · subst h0
    simp
  by_cases h1 : k = 1
  · subst h1
    simp
  by_cases hD : ap (dTab orbLit) k = k
  swap
  · simp [hD]
  by_cases hD1 : ap (treeActTab orbLit (dTab orbLit) (genTables orbLit (-2)) 1) k = k
  swap
  · simp [hD1]
  have hf : wa G wX k = k := by rw [← rw_X.ap hk, ap_comp hk, hD1, hD]
  obtain ⟨c, r, hr', hwk⟩ := orbSl_spec hs k hk (by rw [Nat.zero_add]; exact exU_false h0 h1)
    (by rw [Nat.zero_add]; exact hf)
  rw [Nat.zero_add] at hwk
  have hr39 : r = 39 := hr'.elim id id
  subst hr39
  obtain ⟨-, hn⟩ := orbit_count ok_wX gU_lt h8 (c := c) (r := 39) (by norm_num)
  rw [hwk] at hn
  have hT := rw_compT rw_X (rw_treeActTab hk)
  have hc : fixCount (compT 31671 XBt
      (treeActTab orbLit (dTab orbLit) (genTables orbLit (-2)) k)) = 183 := by
    unfold fixCount
    rw [hT.countP, countP_nfix _ hT.2.1, wp_append, wp_cons, wp_nil, one_mul, lp_big (by omega),
      Nat.add_sub_cancel_left]
    have hc' := nfix_conj (wp wX * cT k) (cT k)
    have e : cT k * (wp wX * cT k) * (cT k)⁻¹ = cT k * wp wX := by group
    rw [e] at hc'
    rw [← hc', hn, hr]
  simp [hc]

theorem inv_main (chunks : Nat) : invChecks orbLit chunks = true := by
  unfold invChecks
  simp only [Bool.and_eq_true]
  obtain ⟨h1, h2, -, -, -, h6⟩ := misc_facts
  obtain ⟨c1, c2, c3⟩ := counts_ok
  obtain ⟨wC, wB, wA⟩ := wordsABC_ok
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, allk_ok⟩, ?_⟩
  · rw [beq_iff_eq, (D_ap (by norm_num)).1]
    exact h1
  · rw [beq_iff_eq, (rw_treeActTab (k := 1) (by norm_num)).ap (by norm_num), wa_cons, wa_nil,
      lf_eq, if_neg (by norm_num : ¬ (129 : Nat) < 128)]
    exact h2
  · rw [c1]
    rfl
  · rw [c2]
    rfl
  · rw [c3]
    rfl
  · have hx : CFSG.Sporadic.Fi23.Native.isIdT XCt = false := by
      rw [Bool.eq_false_iff]
      intro h
      unfold CFSG.Sporadic.Fi23.Native.isIdT at h
      rw [CFSG.KS.TW.allIn_iff] at h
      have h' := h 2 (by norm_num)
      rw [beq_iff_eq, (XC_ap (by norm_num)).1] at h'
      exact h6 h'
    rw [hx]
    rfl
  · exact invOK_all _ _ fun i hi => wA i hi
  · exact invOK_all _ _ fun i hi => wB i hi
  · exact invOK_all _ _ fun i hi => wC i hi
  · apply parAll_of
    intro k hk
    rw [treeTabs_size (by decide)] at hk
    rw [Array.all_eq_true]
    intro j hj
    rw [treeTabs_size (by decide)] at hj
    rw [← getElem!_pos _ j (by rw [treeTabs_size (by decide)]; exact hj)]
    exact leaf14 hk hj

theorem cover_ok : invCertificate 3 = true := by
  unfold invCertificate
  rw [orbitData_eq']
  exact inv_main 3

end CertificateChecks.KernelFi23S

end
