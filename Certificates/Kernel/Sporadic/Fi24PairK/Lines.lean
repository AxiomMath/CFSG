module

public import Certificates.Kernel.Sporadic.Fi24PairK.Checks.W0
public import Certificates.Kernel.Sporadic.Fi24PairK.Checks.W1
public import Certificates.Kernel.Sporadic.Fi24PairK.Checks.W2
public import Certificates.Kernel.Sporadic.Fi24PairK.Checks.W3
public import Certificates.Kernel.Sporadic.Fi24OrbL.Facts
public import Certificates.Kernel.Sporadic.Fi24Net.Letters
public import CFSG.Certificates.Kernel.Spor.Fi24PairKSound
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporFi24Facts
import CFSG.Certificates.Kernel.Common.ForallTree

public section

namespace CertificateChecks.KernelFi24PairK

open CFSG.KC CFSG.KC.Fi24Net CFSG.KC.Fi24NetPt CFSG.KC.Fi24PairK CFSG.KS.Fi24NetPt
  CFSG.KS.Fi24PairPc CFSG.KS.Fi24PairK CFSG.Sporadic.Th CFSG.Sporadic.Fi24 CFSG.Perm
  CFSG.LocalAnalysis.WeakClosure81.SporFi24
open CFSG.KS.Fi24Net hiding NV
open CFSG.KD.Fi24PairK (NV net WL fl nck wck netL lineL nthN)
open CFSG.Sporadic.Fi24Pair.Native

#kc_forall_tree nkAll (fun g => CFSG.KD.Fi24PairK.nck g = true) 27 CFSG.KD.Fi24PairK.Ck.n
#kc_forall_tree wkAll (fun g => CFSG.KD.Fi24PairK.wck g = true) 589 CFSG.KD.Fi24PairK.Ck.w

theorem blt_false {a b : Nat} (h : b ≤ a) : Nat.blt a b = false := by
  cases e : Nat.blt a b
  · rfl
  · rw [Nat.blt_eq] at e
    omega

theorem NV_lt13 {j : Nat} (hj : j < 13) : NV j = CFSG.KD.Fi24Net.NW j := by
  funext l
  unfold NV
  rw [Nat.blt_eq.mpr hj]

theorem net_cases : ∀ j < 90, net j = true → j < 13 ∨ (∃ t < 27, nthN netL t = j) ∨ j = 22 ∨
    j = 24 ∨ j = 25 ∨ j = 26 := by
  decide +kernel

theorem net_ge90 {j : Nat} (hj : 90 ≤ j) : net j = false := by
  unfold net
  rw [blt_false (by omega : 29 ≤ j), blt_false hj]
  cases Nat.ble 75 j <;> rfl

theorem net0 : net 0 = true := rfl

theorem net1 : net 1 = true := rfl

theorem netOK_all : ∀ j, net j = true → netOK (NV j) = true := by
  intro j hj
  by_cases h90 : j < 90
  · rcases net_cases j h90 hj with h | ⟨t, ht, rfl⟩ | rfl | rfl | rfl | rfl
    · rw [NV_lt13 h]
      exact CFSG.KD.Fi24Net.nck_spec j h
    · exact nkAll t ht
    · have e : NV 22 = NV 15 := by funext l; rfl
      rw [e]
      exact nkAll 2 (by norm_num)
    · have e : NV 24 = NV 17 := by funext l; rfl
      rw [e]
      exact nkAll 4 (by norm_num)
    · have e : NV 25 = NV 18 := by funext l; rfl
      rw [e]
      exact nkAll 5 (by norm_num)
    · have e : NV 26 = NV 19 := by funext l; rfl
      rw [e]
      exact nkAll 6 (by norm_num)
  · rw [net_ge90 (by omega)] at hj
    exact absurd hj (by decide)

theorem net_of_dir {z : ℤ} (hz : dirZ net z = true) (h : ¬ z.natAbs ≤ 2) :
    net (z.natAbs - 3) = true := by
  unfold dirZ at hz
  rw [ble_false (by omega : 2 < z.natAbs)] at hz
  exact hz

theorem dir_big {z : ℤ} (hz : dirZ net z = false) : ¬ z.natAbs ≤ 2 := by
  intro h
  unfold dirZ at hz
  have e : Nat.ble z.natAbs 2 = true := Nat.ble_eq.mpr h
  rw [e] at hz
  exact Bool.noConfusion (hz : true = false)

theorem nthW_eq : ∀ (l : List (List Int)) (j : Nat), CFSG.KD.Fi24Net.nthW l j = l.getD j []
  | [], _ => by rw [List.getD_nil]; rfl
  | _ :: _, 0 => by rw [List.getD_cons_zero]; rfl
  | _ :: l, j + 1 => by rw [List.getD_cons_succ]; exact nthW_eq l j

theorem get_neg (A : Array (List Int)) {j : Nat} (h : ¬ j < A.size) : A[j]! = [] := by
  rw [getElem!_neg A j h]
  rfl

theorem toList_getD (A : Array (List Int)) (j : Nat) : A.toList.getD j [] = A[j]! := by
  by_cases h : j < A.size
  · have h' : j < A.toList.length := by rw [Array.length_toList]; exact h
    rw [getElem!_pos A j h, List.getD_eq_getElem _ _ h', Array.getElem_toList]
  · have h' : A.toList.length ≤ j := by rw [Array.length_toList]; omega
    rw [get_neg A h, List.getD_eq_default _ _ h']

theorem W_get_neg {j : Nat} (h : ¬ j < W.size) : W[j]! = [] := get_neg W h

theorem WL_eq (j : Nat) : WL j = W[j]! := by
  unfold CFSG.KD.Fi24PairK.WL
  rw [nthW_eq]
  exact toList_getD W j

theorem W_size : 90 ≤ W.size := by decide +kernel

theorem lineL_of : ∀ j < 90, net j = true → 13 ≤ j → ∃ t < 31, nthN lineL t = j := by
  decide +kernel


theorem genG_one : genG 1 = a := if_pos rfl

theorem genG_neg_one : genG (-1) = a := by
  unfold genG
  rw [if_neg (by decide), if_pos rfl, a_inv]

theorem genG_two : genG 2 = b := by
  unfold genG
  rw [if_neg (by decide), if_neg (by decide), if_pos rfl]

theorem genG_inv {z : ℤ} (h1 : z ≠ 1) (h2 : z ≠ -1) (h3 : z ≠ 2) : genG z = b⁻¹ := by
  unfold genG
  rw [if_neg h1, if_neg h2, if_neg h3]

@[expose] noncomputable def LL (z : ℤ) : J :=
  if z.natAbs ≤ 2 then genG z else if 0 < z then line (z.natAbs - 3) else (line (z.natAbs - 3))⁻¹

theorem LL_inv (z : ℤ) (hz : z ≠ 0) : LL (-z) = (LL z)⁻¹ := by
  unfold LL
  rw [Int.natAbs_neg]
  by_cases h : z.natAbs ≤ 2
  · rw [if_pos h, if_pos h]
    rcases (by omega : z = -2 ∨ z = -1 ∨ z = 1 ∨ z = 2) with rfl | rfl | rfl | rfl
    · rw [neg_neg, genG_two, genG_inv (by decide) (by decide) (by decide), inv_inv]
    · rw [neg_neg, genG_one, genG_neg_one, a_inv]
    · rw [genG_one, genG_neg_one, a_inv]
    · rw [genG_two, genG_inv (by decide) (by decide) (by decide)]
  · rw [if_neg h, if_neg h]
    rcases lt_or_gt_of_ne hz with h' | h'
    · rw [if_pos (by omega : (0 : ℤ) < -z), if_neg (by omega : ¬ (0 : ℤ) < z), inv_inv]
    · rw [if_neg (by omega : ¬ (0 : ℤ) < -z), if_pos h']

theorem LL_ofNat (l : ℕ) : LL (Int.ofNat (l + 3)) = line l := by
  unfold LL
  have e : (Int.ofNat (l + 3)).natAbs = l + 3 := rfl
  rw [e, if_neg (by omega), if_pos (by rw [Int.ofNat_eq_coe]; omega), Nat.add_sub_cancel]

theorem wEl_W (j : ℕ) : wEl LL (W[j]!) = line j := by
  rw [line, CFSG.Sporadic.Fi23.slpG_eq]
  unfold wordG wEl
  by_cases hj : j < W.size
  · refine congrArg List.prod (List.map_congr_left fun z hz => ?_)
    obtain ⟨-, hz1⟩ := W_letter j hj z hz
    unfold LL
    by_cases h2 : z.natAbs ≤ 2
    · rw [if_pos h2, if_pos h2]
    · have hlt : z.natAbs - 3 < j := by have := hz1.resolve_left h2; omega
      rw [if_neg h2, if_neg h2, if_pos hlt]
      rfl
  · rw [W_get_neg hj]
    rfl

theorem idx_gs {j : Nat} (hj : j < 13) {q : Nat} (hq : q < 306936) :
    idx 306936 (gs j) q = pF (CFSG.KD.Fi24Net.NW j) q := by
  have h := CertificateChecks.KernelFi24OrbL.pairG_LN (2 * j) (by omega) q hq
  have e : pairG gs (2 * j) = gs j := by simp [pairG]
  rwa [e, LN_even] at h

theorem idx_gs_inv {j : Nat} (hj : j < 13) {q : Nat} (hq : q < 306936) :
    idx 306936 (gs j)⁻¹ q = pR (CFSG.KD.Fi24Net.NW j) q := by
  have h := CertificateChecks.KernelFi24OrbL.pairG_LN (2 * j + 1) (by omega) q hq
  have e1 : (2 * j + 1) / 2 = j := by omega
  have e : pairG gs (2 * j + 1) = (gs j)⁻¹ := by
    unfold pairG
    rw [if_neg (by omega), e1]
  rwa [e, LN_odd] at h

theorem pt_small {z : ℤ} (hz : z.natAbs ≤ 2) {q : ℕ} (hq : q < 306936) :
    ptZ NV z q = idx 306936 (genG z) q := by
  have h0 : NV 0 = CFSG.KD.Fi24Net.NW 0 := NV_lt13 (by norm_num)
  have h1 : NV 1 = CFSG.KD.Fi24Net.NW 1 := NV_lt13 (by norm_num)
  rcases (by omega : z = -2 ∨ z = -1 ∨ z = 0 ∨ z = 1 ∨ z = 2) with rfl | rfl | rfl | rfl | rfl
  · have e : ptZ NV (-2) q = ptR (NV 1) q := rfl
    rw [e, h1, ptR_eq, genG_inv (by decide) (by decide) (by decide), ← gs_one,
      idx_gs_inv (by norm_num) hq]
  · have e : ptZ NV (-1) q = ptF (NV 0) q := rfl
    rw [e, h0, ptF_eq, genG_neg_one, ← gs_zero, idx_gs (by norm_num) hq]
  · have e : ptZ NV 0 q = ptR (NV 1) q := rfl
    rw [e, h1, ptR_eq, genG_inv (by decide) (by decide) (by decide), ← gs_one,
      idx_gs_inv (by norm_num) hq]
  · have e : ptZ NV 1 q = ptF (NV 0) q := rfl
    rw [e, h0, ptF_eq, genG_one, ← gs_zero, idx_gs (by norm_num) hq]
  · have e : ptZ NV 2 q = ptF (NV 1) q := rfl
    rw [e, h1, ptF_eq, genG_two, ← gs_one, idx_gs (by norm_num) hq]

theorem pt_of_line {m : ℕ} (hm : net m = true)
    (h : ∀ q < 306936, idx 306936 (line m) q = pF (NV m) q) {z : ℤ} (hz : z.natAbs = m + 3) :
    ∀ q < 306936, ptZ NV z q = idx 306936 (LL z) q := by
  intro q hq
  obtain ⟨hv, hpt⟩ := net_spec (netOK_all m hm)
  rw [ptZ_eq_lP]
  unfold LL
  rw [if_neg (by omega), hz, Nat.add_sub_cancel]
  cases z with
  | ofNat n =>
    have hn : n = m + 3 := hz
    subst hn
    have e : lP NV (Int.ofNat (m + 3)) = pF (NV (lidx (m + 3))) := if_neg (by omega)
    rw [e, lidx_ge (by omega), Nat.add_sub_cancel, if_pos (by rw [Int.ofNat_eq_coe]; omega),
      h q hq]
  | negSucc n =>
    have hn : n + 1 = m + 3 := hz
    have e : lP NV (Int.negSucc n) = pR (NV (lidx (n + 1))) := if_neg (by omega)
    rw [e, hn, lidx_ge (by omega), Nat.add_sub_cancel, if_neg (by rw [Int.negSucc_eq]; omega)]
    have hr : pR (NV m) q < 306936 := by
      have := (hpt _ (pR_lt hv (by omega : q < 524288))).1
      rw [pF_pR hv] at this
      exact this hq
    have e2 : q = idx 306936 (line m) (pR (NV m) q) := by rw [h _ hr, pF_pR hv]
    conv_rhs => rw [e2]
    rw [idx_inv_idx]

theorem apZ_eq_of {w : List ℤ} (h : ∀ z ∈ w, ∀ q < 306936, ptZ NV z q = idx 306936 (LL z) q) :
    ∀ q < 306936, apZ NV w q = idx 306936 (wEl LL w) q := by
  induction w with
  | nil =>
    intro q _
    rw [apZ_nil]
    simp [wEl, idx_one]
  | cons z w ih =>
    intro q hq
    rw [apZ_cons, ih (fun z' hz' => h z' (List.mem_cons_of_mem z hz')) q hq, wEl_cons, idx_mul,
      h z List.mem_cons_self _ (idx_lt _ hq)]

theorem pt_line : ∀ j, net j = true → ∀ q < 306936, idx 306936 (line j) q = pF (NV j) q := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  intro hj q hq
  by_cases h13 : j < 13
  · rw [line_eq_gs h13, idx_gs h13 hq, NV_lt13 h13]
  · have h90 : j < 90 := by
      by_contra hc
      rw [net_ge90 (by omega)] at hj
      exact absurd hj (by decide)
    obtain ⟨t, ht, e⟩ := lineL_of j h90 hj (by omega)
    have hw : ∀ k < 19, dirOK net (WL j) = true ∧ wordOK NV (WL j) j k = true := by
      intro k hk
      have hlt : 19 * t + k < 589 := by omega
      have h := wkAll (19 * t + k) hlt
      have e1 : Nat.div (19 * t + k) 19 = t := by
        change (19 * t + k) / 19 = t
        omega
      have e2 : Nat.mod (19 * t + k) 19 = k := by
        change (19 * t + k) % 19 = k
        omega
      unfold CFSG.KD.Fi24PairK.wck at h
      rw [e1, e2, e] at h
      have h' : andB (dirOK net (WL j)) (wordOK NV (WL j) j k) = true := h
      rw [andB_eq, Bool.and_eq_true] at h'
      exact h'
    have hdir := (hw 0 (by norm_num)).1
    have hvj := (net_spec (netOK_all j hj)).1
    have hws := word_spec hvj (fun z hz => nv_dir netOK_all net0 net1 (dirOK_mem hdir z hz))
      fun k hk => (hw k hk).2
    rw [hws q (by omega), foldr_lP_eq, ← wEl_W j, ← WL_eq]
    refine (apZ_eq_of (fun z hz q' hq' => ?_) q hq).symm
    have hzW : z ∈ W[j]! := by rw [← WL_eq]; exact hz
    have hjW : j < W.size := by
      have := W_size
      omega
    obtain ⟨-, hz1⟩ := W_letter j hjW z hzW
    by_cases h2 : z.natAbs ≤ 2
    · unfold LL
      rw [if_pos h2]
      exact pt_small h2 hq'
    · have hm := net_of_dir (dirOK_mem hdir z hz) h2
      exact pt_of_line hm (ih _ (by omega) hm) (by omega) q' hq'

theorem ptHyp : PtHyp LL NV net := by
  intro z hz q hq
  by_cases h2 : z.natAbs ≤ 2
  · unfold LL
    rw [if_pos h2]
    exact pt_small h2 hq
  · have hm := net_of_dir hz h2
    exact pt_of_line hm (pt_line _ hm) (by omega) q hq

theorem fl_eq (j : ℕ) : (∀ y ∈ fl j, y ≠ 0) ∧ wEl LL (fl j) = line j := by
  have hW : ∀ z : ℤ, 0 < z → dirZ net z = false →
      (∀ y ∈ WL (z.natAbs - 3), y ≠ 0) ∧ wEl LL (WL (z.natAbs - 3)) = LL z := by
    intro z hz hd
    have h2 := dir_big hd
    rw [WL_eq, wEl_W]
    refine ⟨fun y hy => ?_, ?_⟩
    · by_cases hs : z.natAbs - 3 < W.size
      · exact (W_letter _ hs y hy).1
      · rw [W_get_neg hs] at hy
        exact absurd hy List.not_mem_nil
    · unfold LL
      rw [if_neg h2, if_pos hz]
  have h := flatF_spec LL_inv hW 8 (Int.ofNat (j + 3)) (by rw [Int.ofNat_eq_coe]; omega)
  rw [LL_ofNat] at h
  exact h

end CertificateChecks.KernelFi24PairK

end
