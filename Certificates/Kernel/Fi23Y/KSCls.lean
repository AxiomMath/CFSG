module

public import Certificates.Kernel.Fi23Y.KSSyl
public import Certificates.Kernel.Fi23S.Fact1014
import CFSG.Certificates.Kernel.Spor.RawOrbEval
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicFi23Tests

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi23Y.KSC

open CFSG.KC.Enum CFSG.KC.Fi23K CFSG.KC.Fi23R CFSG.KC.Fi23S CFSG.KD.Fi23K CFSG.KD.Fi23S
  CFSG.KD.Fi23R CFSG.KS.Raw.Orb CFSG.KS.TBfs CFSG.KS.PC CFSG.KS.PEnum CFSG.Sporadic.Fi23.Native
  CFSG.Sporadic.Th.Native CFSG.Perm.Native CertificateChecks.KernelFi23R
  CertificateChecks.KernelFi23M CertificateChecks.KernelFi23S CertificateChecks.KernelFi23Y.KSY
open CFSG.ComponentClassification.RankTwoSporadic.RootCensus (fixP fixP_conj)
open CFSG.ComponentClassification.RankTwoSporadic.Fi23 (fi23Fix)

private theorem conj_odd {M : Type*} [Group M] {s r : M} (hs : s ^ 2 = 1) (hr : r ^ 2 = 1)
    {m : ℕ} (hm : m % 2 = 1) (h : (s * r) ^ m = 1) : ∃ c : M, c * r * c⁻¹ = s := by
  have hr2 : r * r = 1 := by rw [← pow_two, hr]
  have hri : r⁻¹ = r := inv_eq_of_mul_eq_one_right hr2
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right (by rw [← pow_two, hs])
  have h1 : r * (s * r)⁻¹ = s * r * r := by
    rw [mul_inv_rev, hri, hsi, ← mul_assoc, hr2, one_mul, mul_assoc, hr2, mul_one]
  have h2 : ∀ j : ℕ, r * ((s * r)⁻¹) ^ j = (s * r) ^ j * r := by
    intro j
    induction j with
    | zero => rw [pow_zero, pow_zero, mul_one, one_mul]
    | succ j ih =>
      calc r * ((s * r)⁻¹) ^ (j + 1) = r * (s * r)⁻¹ * ((s * r)⁻¹) ^ j := by
            rw [pow_succ', mul_assoc]
        _ = s * r * (r * ((s * r)⁻¹) ^ j) := by rw [h1, mul_assoc]
        _ = (s * r) ^ (j + 1) * r := by rw [ih, ← mul_assoc, ← pow_succ']
  obtain ⟨k, rfl⟩ : ∃ k, m = 2 * k + 1 := ⟨m / 2, by omega⟩
  refine ⟨(s * r) ^ (k + 1), ?_⟩
  rw [mul_assoc, ← inv_pow, h2, ← mul_assoc, ← pow_add,
    show k + 1 + (k + 1) = 2 * k + 1 + 1 by ring, pow_succ, h, one_mul, mul_assoc, hr2, mul_one]

private theorem sq_comm {M : Type*} [Group M] {a b : M} (ha : a * a = 1) (hb : b * b = 1)
    (h : a * b = b * a) : a * b * (a * b) = 1 := by
  rw [← mul_assoc, mul_assoc a b a, ← h, ← mul_assoc, ha, one_mul, hb]

private theorem wX_eq : wp wX = dP * cT 1 := by
  have e : lp 129 = cT 1 := lp_big (c := 129) (by norm_num)
  rw [show wX = [129, 43] from rfl, wp_cons, wp_cons, wp_nil, one_mul, lp_43, e]

private theorem wXC_eq : wp wXC = wp wX * cT 39 := by
  have e : lp 167 = cT 39 := lp_big (c := 167) (by norm_num)
  rw [show wXC = 167 :: wX from rfl, wp_cons, e]

private theorem cT_sq (k : ℕ) :
    cT k * cT k = 1 :=
  mul_eq_one_iff_eq_inv.2 (cT_inv dP_sq k).symm

private theorem d_d1 :
    dP * cT 1 = cT 1 * dP := by
  have h0 : cmB wX 0 = true := List.all_eq_true.1 base_facts.2.2.2.2.2.2.2.1 0 List.mem_cons_self
  have hc := cmB_comm ok_wX (g := 0) (by norm_num) h0
  rw [cT_zero, wX_eq] at hc
  calc dP * cT 1 = dP * cT 1 * dP * dP := by rw [mul_assoc (dP * cT 1), dP_sq, mul_one]
    _ = dP * (dP * cT 1) * dP := by rw [hc]
    _ = cT 1 * dP := by rw [← mul_assoc, dP_sq, one_mul]

private theorem comm_c39 (h : PG)
    (hfix : (phiX h ⟨39, by norm_num⟩).val = 39) : phiX h * cT 39 = cT 39 * phiX h := by
  have e := cT_conj h (k := 39) (by norm_num)
  rw [hfix] at e
  exact mul_inv_eq_iff_eq_mul.1 e

private theorem d_c39 :
    dP * cT 39 = cT 39 * dP := by
  have hf : (dP ⟨39, by norm_num⟩).val = 39 := by
    rw [dP_acts 39 (by norm_num)]
    exact misc_facts.1
  exact comm_c39 wD hf

private theorem d1_c39 :
    cT 1 * cT 39 = cT 39 * cT 1 := by
  have hf : (cT 1 ⟨39, by norm_num⟩).val = 39 := by
    rw [cT_acts (k := 1) (by norm_num) 39 (by norm_num)]
    exact misc_facts.2.1
  exact comm_c39 (tk 1 * wD * (tk 1)⁻¹) hf

private theorem X_c39 :
    wp wX * cT 39 = cT 39 * wp wX := by
  rw [wX_eq, mul_assoc, d1_c39, ← mul_assoc, d_c39, mul_assoc]

private theorem wX_sq :
    wp wX * wp wX = 1 := by
  rw [wX_eq]
  exact sq_comm dP_sq (cT_sq 1) d_d1

private theorem wXC_sq :
    wp wXC * wp wXC = 1 := by
  rw [wXC_eq]
  exact sq_comm wX_sq (cT_sq 39) X_c39

private noncomputable def xR (r : ℕ) : Pt := if r < 17 then wp wXC else if r < 27 then wp wX else dP

private theorem xR_mem (r : ℕ) : xR r ∈ Xc := by
  unfold xR
  split_ifs
  · exact wp_mem _
  · exact wp_mem _
  · rw [← lp_43]
    exact lp_mem 43

private theorem xR_sq (r : ℕ) :
    xR r * xR r = 1 := by
  unfold xR
  split_ifs
  · exact wXC_sq
  · exact wX_sq
  · exact dP_sq

private theorem xR_acts (r : ℕ) :
    ActsAs (xR r) (xEv r) := by
  unfold xR
  split_ifs with h1 h2
  · refine actsAs_congr (wp_acts wXC ok_wXC) fun y hy => ?_
    rw [xEv_C h1, ← rw_XC.ap hy]
    exact (XC_ap hy).1
  · refine actsAs_congr (wp_acts wX ok_wX) fun y hy => ?_
    rw [xEv_B (by omega) h2, ← rw_X.ap hy]
    exact (XB_ap hy).1
  · refine actsAs_congr dP_acts fun y _ => ?_
    rw [xEv_A (by omega)]

private theorem ur_ok (r : ℕ)
    (hr : r < 29) : ∃ u : List ℕ, (∀ c ∈ u, okL c) ∧
      List.getD UR r [] = u ∧ List.getD URi r [] = invW u := by
  obtain ⟨uC, uB, uA⟩ := UR_eq
  obtain ⟨wC, wB, wA⟩ := wordsABC_ok
  have hok : ∀ w : List ℤ, (∀ z ∈ w, z = 1 ∨ z = -1 ∨ z = 2 ∨ z = -2) →
      ∀ c ∈ w.reverse.map regZ, okL c := by
    intro w hw c hc
    obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hc
    exact okL_regZ (hw z (List.mem_reverse.1 hz))
  rcases (by omega : r < 17 ∨ (17 ≤ r ∧ r < 27) ∨ 27 ≤ r) with h | h | h
  · exact ⟨_, hok _ (wC r h), (uC r h).1, (uC r h).2⟩
  · obtain ⟨i, rfl⟩ : ∃ i, r = 17 + i := ⟨r - 17, by omega⟩
    exact ⟨_, hok _ (wB i (by omega)), (uB i (by omega)).1, (uB i (by omega)).2⟩
  · obtain ⟨i, rfl⟩ : ∃ i, r = 27 + i := ⟨r - 27, by omega⟩
    exact ⟨_, hok _ (wA i (by omega)), (uA i (by omega)).1, (uA i (by omega)).2⟩

private theorem repeat_actN {h : ℕ → ℕ} {p : Pt} (hh : ∀ y < 31671, h y = actN p y) :
    ∀ n, ∀ q < 31671, Nat.repeat h n q = actN (p ^ n) q
  | 0, q, _ => by
    show q = actN (p ^ 0) q
    rw [pow_zero, actN_one]
  | n + 1, q, hq => by
    rw [Nat.repeat, repeat_actN hh n q hq, hh _ (actN_lt _ hq), pow_succ', actN_mul]

private theorem odd_of_cyc
    {h : ℕ → ℕ} {p : Pt} (hp : p ∈ Xc) (hh : ∀ y < 31671, h y = actN p y)
    (hc : ∀ q < 6, cyK h q 119 1 (h q) % 2 = 1) : ∃ L, L % 2 = 1 ∧ p ^ L = 1 := by
  have hfix : ∀ q < 6, Nat.repeat h (cyK h q 119 1 (h q)) q = q := fun q hq => by
    have h1 := hc q hq
    obtain ⟨-, hr⟩ := cyK_spec h q 119 1 (h q) _ rfl (by omega)
    generalize cyK h q 119 1 (h q) = c at hr h1 ⊢
    have e : c = (c - 1) + 1 := by omega
    rw [e, repeat_add]
    exact hr
  have hall : ∀ q ∈ [0, 1, 2, 3, 4, 5], (fun q => cyK h q 119 1 (h q)) q % 2 = 1 :=
    fun q hq => hc q (by simp at hq; omega)
  refine ⟨_, foldl_odd (fun q => cyK h q 119 1 (h q)) [0, 1, 2, 3, 4, 5] 1 rfl hall, ?_⟩
  refine one_of_fix (Subgroup.pow_mem _ hp _) fun q hq => ?_
  rw [← repeat_actN hh _ q (by omega)]
  exact repeat_dvd h (hfix q hq)
    ((foldl_dvd (fun q => cyK h q 119 1 (h q)) [0, 1, 2, 3, 4, 5] 1).2 q (by simp; omega))

private theorem fixP_eq_nfix (p : Pt) : fixP p = nfix p := by
  unfold fixP nfix
  exact Fintype.card_subtype _

private theorem fix_C :
    fixP (wp wXC) = 183 := by
  rw [fixP_eq_nfix, ← countP_nfix _ ok_wXC, ← rw_XC.countP]
  have := counts_ok.2.2
  unfold fixCount at this
  exact this

private theorem fix_B :
    fixP (wp wX) = 695 := by
  rw [fixP_eq_nfix, ← countP_nfix _ ok_wX, ← rw_X.countP]
  have := counts_ok.2.1
  unfold fixCount at this
  exact this

private theorem fix_D :
    fixP dP = 3511 := by
  have e : wp [43] = dP := by rw [wp_cons, wp_nil, one_mul, lp_43]
  rw [← e, fixP_eq_nfix, ← countP_nfix _ (by decide), ← rw_dTab.countP]
  have := counts_ok.1
  unfold fixCount at this
  exact this

private theorem fixP_eq_xR
    {l : ℕ} (hl : l < 262144) (hc : 2 ≤ CFSG.KD.Fi23Y.CD l) (h2 : lvP l ^ 2 = 1) :
    fixP (lvP l) = fixP (xR ((CFSG.KD.Fi23Y.CD l - 2) / 4)) := by
  have hk : l / 512 < 512 := leaf_hi_lt hl
  have hj : l % 512 < 512 := leaf_lo_lt l
  rw [CD_eq] at hc ⊢
  obtain ⟨hr, hcyc⟩ := lf14_cases (lf14_all hk hj) hc
  generalize (code (l / 512) (l % 512) - 2) / 4 = r at hr hcyc ⊢
  obtain ⟨u, hu, eU, eUi⟩ := ur_ok r hr
  have hRm : wp u * xR r * (wp u)⁻¹ ∈ Xc :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (wp_mem u) (xR_mem r)) (Subgroup.inv_mem _ (wp_mem u))
  have hRa : ActsAs (wp u * xR r * (wp u)⁻¹) (rEv r) := by
    rw [← wp_invW dP_sq u hu]
    refine actsAs_congr (((wp_acts u hu).mul (xR_acts r)).mul (wp_acts (invW u) (ok_invW hu)))
      fun y _ => ?_
    unfold rEv
    rw [eU, eUi]
  have hR2 : (wp u * xR r * (wp u)⁻¹) ^ 2 = 1 := by
    rw [pow_two, show wp u * xR r * (wp u)⁻¹ * (wp u * xR r * (wp u)⁻¹) =
      wp u * (xR r * xR r) * (wp u)⁻¹ by group, xR_sq, mul_one, mul_inv_cancel]
  have hP : ∀ y < 31671,
      hK (l / 512) (l % 512) r y = actN (lvP l * (wp u * xR r * (wp u)⁻¹)) y := by
    intro y hy
    have e1 : actN (wp u * xR r * (wp u)⁻¹) y = rEv r y := by
      rw [actN_eq_val _ hy]
      exact hRa y hy
    have hlt : rEv r y < 31671 := by
      rw [← e1]
      exact actN_lt _ hy
    rw [actN_mul, e1]
    unfold hK
    rw [lvP_eq]
    exact gK_eq hk hj hlt
  obtain ⟨L, hL, hLp⟩ := odd_of_cyc (Subgroup.mul_mem _ (lvP_mem hl) hRm) hP hcyc
  obtain ⟨c, hc'⟩ := conj_odd h2 hR2 hL hLp
  rw [← hc', fixP_conj, fixP_conj]

private theorem clsY_eq (cd : ℕ → ℕ) (l : ℕ) : CFSG.KC.Fi23Y.clsY cd l =
    if (cd l - 2) / 4 < 17 then 2 else if (cd l - 2) / 4 < 27 then 1 else 0 := by
  have e : Nat.shiftRight (Nat.sub (cd l) (nat_lit 2)) (nat_lit 2) = (cd l - 2) / 4 := by
    change (cd l - 2) >>> 2 = _
    rw [Nat.shiftRight_eq_div_pow]
  unfold CFSG.KC.Fi23Y.clsY
  rw [strictN_eq, e, nIf_eq, nIf_eq]
  by_cases h1 : (cd l - 2) / 4 < 17
  · rw [if_pos (Nat.blt_eq.mpr h1), if_pos h1]
  · by_cases h2 : (cd l - 2) / 4 < 27
    · rw [if_neg (by rw [Nat.blt_eq]; exact h1), if_pos (Nat.blt_eq.mpr h2), if_neg h1, if_pos h2]
    · rw [if_neg (by rw [Nat.blt_eq]; exact h1), if_neg (by rw [Nat.blt_eq]; exact h2), if_neg h1,
        if_neg h2]

theorem fixP_lvP {l : ℕ}
    (hl : l < 262144) (hc : 2 ≤ CFSG.KD.Fi23Y.CD l) (h2 : lvP l ^ 2 = 1) :
    fixP (lvP l) = fi23Fix[CFSG.KC.Fi23Y.clsY CFSG.KD.Fi23Y.CD l]! := by
  rw [fixP_eq_xR hl hc h2, clsY_eq]
  unfold xR
  by_cases h1 : (CFSG.KD.Fi23Y.CD l - 2) / 4 < 17
  · rw [if_pos h1, if_pos h1, fix_C, (by decide : fi23Fix[2]! = 183)]
  · by_cases h3 : (CFSG.KD.Fi23Y.CD l - 2) / 4 < 27
    · rw [if_neg h1, if_pos h3, if_neg h1, if_pos h3, fix_B, (by decide : fi23Fix[1]! = 695)]
    · rw [if_neg h1, if_neg h3, if_neg h1, if_neg h3, fix_D, (by decide : fi23Fix[0]! = 3511)]

end CertificateChecks.KernelFi23Y.KSC

end
