
module

public import Certificates.Kernel.Fi23Q.Regs
public import Certificates.Kernel.Fi23Q.WordDefs
public import CFSG.Certificates.Kernel.Fi23Q.WordSound
import Certificates.Kernel.Fi23Q.Words
import Certificates.Kernel.Fi23Q.WordsAll

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi23Q

open CFSG.Sporadic.Fi23 CFSG.Sporadic.Th CFSG.KC.Fi23K CFSG.KC.Fi23Q CFSG.KC.Pc3 CFSG.KD.Fi23K
  CFSG.Perm CFSG.KS.Raw.Orb
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23 (zJ t3)
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Sylow (qG eq_of_base)
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Native (kleinZ qWords)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem chain_ok {w : List ℕ} (h : ∀ l ∈ w, l < 24) : ∀ r ∈ w.map (Nat.add 52), RegOK r := by
  intro r hr
  obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hr
  have := h l hl
  right
  change 52 ≤ 52 + l ∧ 52 + l < 76
  omega

theorem chain_prod (w : List ℕ) :
    ((w.map (Nat.add 52)).map regE).prod = (w.map (pairG gs)).prod := by
  rw [List.map_map]
  congr 1
  exact List.map_congr_left fun l _ => regE_letter l

theorem zR_ok : ∀ r ∈ CFSG.KD.Fi23Q.zR, RegOK r := chain_ok (by decide)

theorem zR_prod : (CFSG.KD.Fi23Q.zR.map regE).prod = zJ :=
  chain_prod kleinZ

theorem qR_eq : CFSG.KD.Fi23Q.qR0 = (qWords[0]!).map (Nat.add 52) ∧
    CFSG.KD.Fi23Q.qR1 = (qWords[1]!).map (Nat.add 52) ∧
    CFSG.KD.Fi23Q.qR2 = (qWords[2]!).map (Nat.add 52) := by
  decide

theorem qWords_lt : ∀ j < 3, ∀ l ∈ qWords[j]!, l < 24 := by decide

theorem comm_of_eqH
    {q : List ℕ} (hq : ∀ l ∈ q, l < 24)
    (h : eqH G (CFSG.KD.Fi23Q.zR ++ q.map (Nat.add 52)) (q.map (Nat.add 52) ++ CFSG.KD.Fi23Q.zR)
      = true) : zJ * (q.map (pairG gs)).prod = (q.map (pairG gs)).prod * zJ := by
  apply eq_of_base
  intro t ht
  have e := eqH_spec h t ht
  have hok : ∀ r ∈ CFSG.KD.Fi23Q.zR ++ q.map (Nat.add 52), RegOK r := fun r hr =>
    (List.mem_append.1 hr).elim (zR_ok r) (chain_ok hq r)
  have hok' : ∀ r ∈ q.map (Nat.add 52) ++ CFSG.KD.Fi23Q.zR, RegOK r := fun r hr =>
    (List.mem_append.1 hr).elim (chain_ok hq r) (zR_ok r)
  rw [wvG_eq _ hok t (by omega), wvG_eq _ hok' t (by omega), List.map_append, List.map_append,
    List.prod_append, List.prod_append, zR_prod, chain_prod] at e
  exact e

theorem z_comm
    {j : ℕ} (hj : j < 3) : zJ * qG j = qG j * zJ := by
  have hz := CFSG.KD.Fi23Q.zK_ok
  unfold CFSG.KD.Fi23Q.zK at hz
  rw [bAnd_eq, bAnd_eq, Bool.and_eq_true, Bool.and_eq_true] at hz
  obtain ⟨h0, h1, h2⟩ := hz
  obtain ⟨e0, e1, e2⟩ := qR_eq
  interval_cases j
  · rw [e0] at h0
    exact comm_of_eqH (qWords_lt 0 (by norm_num)) h0
  · rw [e1] at h1
    exact comm_of_eqH (qWords_lt 1 (by norm_num)) h1
  · rw [e2] at h2
    exact comm_of_eqH (qWords_lt 2 (by norm_num)) h2

theorem img_two_eq :
    CFSG.Sporadic.Bridge.Fi23.img 2 = conjPt 30132 :=
  eq_of_base fun t ht => by
    rw [img_acts (by norm_num) t (by omega), tcB_spec CFSG.KD.Fi23Q.t2K_ok t ht,
      conjPt_acts (by norm_num) t (by omega)]

theorem t2_isConj_d :
    IsConj d (CFSG.Sporadic.Bridge.Fi23.img 2) := by
  rw [img_two_eq]
  exact (isConj_d_iff _).2 ⟨⟨30132, by norm_num⟩, rfl⟩

theorem regE_img {r : ℕ} (hr : r < 10) :
    regE r = CFSG.Sporadic.Bridge.Fi23.img r :=
  if_pos hr

theorem t3R_ok {c : ℕ} (hc : c < 4) : ∀ r ∈ CFSG.KD.Fi23Q.t3R c, RegOK r := by
  intro r hr
  interval_cases c
  · change r ∈ [2, 3] at hr
    left
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    omega
  · exact zR_ok r hr
  · change r ∈ [4, 5, 2, 1] at hr
    left
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    omega
  · change r ∈ [5, 3, 7, 0, 6, 1] at hr
    left
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    omega

theorem t3R_prod {c : ℕ} (hc : c < 4) :
    ((CFSG.KD.Fi23Q.t3R c).map regE).prod = t3 ⟨c, hc⟩ := by
  have h0 := regE_img (r := 0) (by norm_num)
  have h1 := regE_img (r := 1) (by norm_num)
  have h2 := regE_img (r := 2) (by norm_num)
  have h3 := regE_img (r := 3) (by norm_num)
  have h4 := regE_img (r := 4) (by norm_num)
  have h5 := regE_img (r := 5) (by norm_num)
  have h6 := regE_img (r := 6) (by norm_num)
  have h7 := regE_img (r := 7) (by norm_num)
  interval_cases c
  · change ([2, 3].map regE).prod =
      CFSG.Sporadic.Bridge.Fi23.img 2 * CFSG.Sporadic.Bridge.Fi23.img 3
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, h2, h3]
  · exact zR_prod
  · change ([4, 5, 2, 1].map regE).prod =
      CFSG.Sporadic.Bridge.Fi23.img 4 * CFSG.Sporadic.Bridge.Fi23.img 5 *
        CFSG.Sporadic.Bridge.Fi23.img 2 * CFSG.Sporadic.Bridge.Fi23.img 1
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, h4, h5, h2, h1,
      mul_assoc]
  · change ([5, 3, 7, 0, 6, 1].map regE).prod =
      CFSG.Sporadic.Bridge.Fi23.img 5 * CFSG.Sporadic.Bridge.Fi23.img 3 *
        CFSG.Sporadic.Bridge.Fi23.img 7 * CFSG.Sporadic.Bridge.Fi23.img 0 *
          CFSG.Sporadic.Bridge.Fi23.img 6 * CFSG.Sporadic.Bridge.Fi23.img 1
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, h5, h3, h7, h0,
      h6, h1, mul_assoc]

theorem cr_conj
    (aE : ℕ → CFSG.Sporadic.Fi23.J)
    (hH : ∀ k < 13, ∀ x < 31671, tb CFSG.KD.Fi23Q.H k x = idx 31671 (aE k) x) :
    ∀ q < 198, ∃ c : Fin 4,
      IsConj (((nwR 13 (f32 CFSG.KD.Fi23Q.CR q)).map aE).prod) (t3 c) := by
  intro q hq
  obtain ⟨c, n, W, h⟩ := CFSG.KD.Fi23Q.cw_all q (Nat.zero_le q) hq
  obtain ⟨-, hc, hw, hb⟩ := clsW_spec h
  have hwok : ∀ r ∈ cwR n W, RegOK r := fun r hr => by
    obtain ⟨l, hl, rfl⟩ := hw r hr
    right
    omega
  set E := ((nwR 13 (f32 CFSG.KD.Fi23Q.CR q)).map aE).prod with hE
  set Wd := ((cwR n W).map regE).prod with hWd
  have key : Wd * E = t3 ⟨c, hc⟩ * Wd := eq_of_base fun t ht => by
    have ht' : t < 31671 := by omega
    have e := hb t ht
    have k1 : wv CFSG.KD.Fi23Q.H (nwR 13 (f32 CFSG.KD.Fi23Q.CR q)) t = idx 31671 E t :=
      wv_eq_of (P := fun r => r < 13) (fun r hr => hH r hr) _ (fun r hr => nwR_lt hr) t ht'
    have k2 : wv G (cwR n W) (idx 31671 E t) = idx 31671 Wd (idx 31671 E t) :=
      wvG_eq _ hwok _ (idx_lt E ht')
    have k3 : wv G (cwR n W) t = idx 31671 Wd t := wvG_eq _ hwok t ht'
    have k4 : wv G (CFSG.KD.Fi23Q.t3R c) (idx 31671 Wd t) =
        idx 31671 (t3 ⟨c, hc⟩) (idx 31671 Wd t) := by
      rw [wvG_eq _ (t3R_ok hc) _ (idx_lt Wd ht'), t3R_prod hc]
    rw [k1, k2, k3, k4] at e
    rw [idx_mul, idx_mul]
    exact e
  exact ⟨⟨c, hc⟩, isConj_iff.2 ⟨Wd, by rw [key, mul_inv_cancel_right]⟩⟩

theorem conj_t3_of
    (aE : ℕ → CFSG.Sporadic.Fi23.J)
    (hH : ∀ k < 13, ∀ x < 31671, tb CFSG.KD.Fi23Q.H k x = idx 31671 (aE k) x)
    {q : ℕ} (hq : q < 198) {x w : CFSG.Sporadic.Fi23.J}
    (h : x * w = w * ((nwR 13 (f32 CFSG.KD.Fi23Q.CR q)).map aE).prod) :
    ∃ c : Fin 4, IsConj x (t3 c) := by
  obtain ⟨c, hc⟩ := cr_conj aE hH q hq
  refine ⟨c, IsConj.trans (isConj_iff.2 ⟨w⁻¹, ?_⟩) hc⟩
  rw [inv_inv, mul_assoc, h, ← mul_assoc, inv_mul_cancel, one_mul]

end CertificateChecks.KernelFi23Q

end
