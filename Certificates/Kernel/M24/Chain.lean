module

public import CFSG.Certificates.Kernel.LceSTabSound
public import CFSG.Certificates.Kernel.BindSubSound
public import CFSG.Certificates.Kernel.CosetBounds
public import CFSG.Certificates.Kernel.Common.BindMap
public import CFSG.Certificates.Kernel.J4.M24Chain.Data.Old_Sel
public import Certificates.Kernel.Co2.Join
public import Certificates.Kernel.Co2.Intro
public import CFSG.Certificates.Kernel.J4.M24Chain.Checks.S1_H_0
public import CFSG.Certificates.Kernel.J4.M24Chain.Checks.S1_W_0
public import CFSG.Certificates.Kernel.J4.M24Chain.Checks.S1_W_1
public import CFSG.Certificates.Kernel.J4.M24Chain.Checks.S1_W_2
public import CFSG.Certificates.Kernel.J4.M24Chain.Checks.S1_W_3
public import CFSG.Certificates.Kernel.J4.M24Chain.Checks.S1_C_0
public import CFSG.Certificates.Kernel.J4.M24Chain.Checks.S1_C_1
public import CFSG.Certificates.Kernel.J4.M24Chain.Checks.S2_H_0
public import CFSG.Certificates.Kernel.J4.M24Chain.Checks.S2_W_0
public import CFSG.Certificates.Kernel.J4.M24Chain.Checks.S2_C_0
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Data.ZMod.QuotientGroup

public section

namespace CertificateChecks.KernelBounds.M24C

open CFSG.KC CFSG.KC.LceS CFSG.KC.Bind CFSG.Certificates CFSG.Certificates.LCE
  CertificateChecks.KernelCo2

#kc_join_range S1facts CertificateChecks.KernelCo2.runFacts_append CFSG.KD.M24S1 "sW" 0 288
#kc_join_range S1cover CertificateChecks.KernelCo2.runCover_append CFSG.KD.M24S1 "sC" 0 92

@[expose] def ord (i : ℕ) : ℕ := [2, 3, 5, 6, 0, 1, 4].getD i 0

@[expose] noncomputable def relMap : ℕ := ofPairs [(0, 4), (1, 5), (2, 0), (3, 1), (4, 6), (5, 2), (6, 3)]

@[expose] def s1idx (r : ℕ) : ℕ := [1, 2, 4, 5, 11, 12, 18, 20, 25, 27, 28].getD r 0

@[expose] noncomputable def letsLt (W n b : ℕ) : Bool := (List.range n).all fun q => Nat.blt (wLet W q) b

theorem letsLt_spec {W n b : ℕ} (h : letsLt W n b = true) : ∀ q < n, wLet W q < b := by
  intro q hq
  have := List.all_eq_true.mp h q (List.mem_range.mpr hq)
  exact Nat.blt_eq.mp this

theorem hM {G : Type*} [Group G] (h : ℕ → G) :
    ∀ g < 7, mget relMap g < 255 → mget relMap g < 127 ∧ h (ord (mget relMap g)) = h g := by
  intro g hg _
  interval_cases g
  · rw [Nat.eq_of_beq_eq_true (by quickRfl : Nat.beq (mget relMap 0) 4 = true)]
    exact ⟨by norm_num, rfl⟩
  · rw [Nat.eq_of_beq_eq_true (by quickRfl : Nat.beq (mget relMap 1) 5 = true)]
    exact ⟨by norm_num, rfl⟩
  · rw [Nat.eq_of_beq_eq_true (by quickRfl : Nat.beq (mget relMap 2) 0 = true)]
    exact ⟨by norm_num, rfl⟩
  · rw [Nat.eq_of_beq_eq_true (by quickRfl : Nat.beq (mget relMap 3) 1 = true)]
    exact ⟨by norm_num, rfl⟩
  · rw [Nat.eq_of_beq_eq_true (by quickRfl : Nat.beq (mget relMap 4) 6 = true)]
    exact ⟨by norm_num, rfl⟩
  · rw [Nat.eq_of_beq_eq_true (by quickRfl : Nat.beq (mget relMap 5) 2 = true)]
    exact ⟨by norm_num, rfl⟩
  · rw [Nat.eq_of_beq_eq_true (by quickRfl : Nat.beq (mget relMap 6) 3 = true)]
    exact ⟨by norm_num, rfl⟩

theorem oldOK : ∀ r < 29, Nat.blt (wWord (CFSG.KD.M24B.selRT r))
    (2 ^ (8 * wLen (CFSG.KD.M24B.selRT r))) = true ∧
    letsLt (wWord (CFSG.KD.M24B.selRT r)) (wLen (CFSG.KD.M24B.selRT r)) 14 = true := by
  intro r hr
  interval_cases r <;> exact ⟨by quickRfl, by quickRfl⟩

theorem rename {G : Type*} [Group G] (h : ℕ → G)
    (hrels : ∀ r < 29, bval h (wWord (CFSG.KD.M24B.selRT r)) (wLen (CFSG.KD.M24B.selRT r)) = 1)
    {r C : ℕ} (hr : r < 29) (hs : subRel relMap (CFSG.KD.M24B.selRT r) C = true) :
    bval (fun i => h (ord i)) (wWord C) (wLen C) = 1 := by
  obtain ⟨hP, hl⟩ := oldOK r hr
  rw [BindSub.subRel_sound h (fun i => h (ord i)) (nG := 7) hs (by norm_num) (Nat.blt_eq.mp hP)
    (letsLt_spec hl) (hM h)]
  exact hrels r hr

theorem bval_list {G : Type*} [Group G] (gen : ℕ → G) (W : ℕ) (l : List ℕ)
    (h : ∀ q < l.length, wLet W q = l.getD q 0) :
    bval gen W l.length = (l.map (letV gen)).prod := by
  unfold bval
  congr 1
  apply List.ext_getElem (by simp)
  intro q h1 h2
  simp only [List.length_map, List.length_range] at h1
  simp [h q h1, List.getElem?_eq_getElem h1]

theorem image_one {G : Type*} [Group G] (gen : ℕ → G) {lit : ℕ → ℕ} {n : ℕ} (hn : n < 127)
    (h : ∀ j < n, lit j = 4 + 4096 * (2 * j)) :
    (fun j => bval gen (wWord (lit j)) (wLen (lit j))) '' {j | j < n} = gen '' {g | 2 * g < 2 * n} := by
  have one : ∀ j < 127, bval gen (wWord (4 + 4096 * (2 * j))) (wLen (4 + 4096 * (2 * j))) = gen j := by
    intro j hj
    have h1 : wWord (4 + 4096 * (2 * j)) = 2 * j := by
      change (4 + 4096 * (2 * j)) >>> 12 = _
      rw [Nat.shiftRight_eq_div_pow]
      omega
    have h2 : wLen (4 + 4096 * (2 * j)) = 1 := by
      change ((4 + 4096 * (2 * j)) >>> 2) &&& (2 ^ 10 - 1) = _
      rw [Nat.shiftRight_eq_div_pow, Nat.and_two_pow_sub_one_eq_mod]
      omega
    have e1 : wLet (2 * j) 0 = 2 * j := by
      rw [BindSub.wLet_eq']
      omega
    have := bval_list gen (2 * j) [2 * j] (fun q hq => by
      change q < 1 at hq
      interval_cases q
      exact e1)
    rw [h1, h2]
    change bval gen (2 * j) [2 * j].length = _
    rw [this]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, letV]
    have e2 : ¬ 2 * j = 255 := by omega
    have e3 : 2 * j % 2 = 0 := by omega
    have e4 : 2 * j / 2 = j := by omega
    simp only [e2, e3, e4, ↓reduceIte]
  ext x
  simp only [Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, by omega, by rw [h j hj, one j (by omega)]⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, by omega, by rw [h j (by omega), one j (by omega)]⟩

theorem card_le {G : Type*} [Group G] (h : ℕ → G)
    (hrels : ∀ r < 29, bval h (wWord (CFSG.KD.M24B.selRT r)) (wLen (CFSG.KD.M24B.selRT r)) = 1) :
    Nat.card (Subgroup.closure (h '' {i | i < 7})) ≠ 0 ∧
      Nat.card (Subgroup.closure (h '' {i | i < 7})) ≤ 23 * (88704 * 5) := by
  set h' : ℕ → G := fun i => h (ord i) with h'_def
  have h1 := lceOk_intro (nR := nat_lit 11) (nS := nat_lit 1) CFSG.KD.M24S1.sH1 CFSG.KD.M24S1.sH0
    (by quickRfl) CFSG.KD.M24S1.sH2 CFSG.KD.M24S1.sH3 (by quickRfl) (by quickRfl) (by quickRfl)
    (by quickRfl) (by quickRfl) (by quickRfl) S1facts (by quickRfl) (by quickRfl) S1cover
    (by quickRfl)
  have hr1 : ∀ r < 11, bval h' (wWord (CFSG.KD.M24S1.selRT r)) (wLen (CFSG.KD.M24S1.selRT r)) = 1 := by
    intro r hr
    have hs : ∀ r < 11, subRel relMap (CFSG.KD.M24B.selRT (s1idx r)) (CFSG.KD.M24S1.selRT r) = true := by
      intro r hr
      interval_cases r <;> quickRfl
    exact rename h hrels (by interval_cases r <;> decide) (hs r hr)
  have s1 := lceOk_sound h1 h' hr1
  have h2 := lceOk_intro (nR := nat_lit 29) (nS := nat_lit 4) CFSG.KD.M24S2.sH1 CFSG.KD.M24S2.sH0
    (by quickRfl) CFSG.KD.M24S2.sH2 CFSG.KD.M24S2.sH3 (by quickRfl) (by quickRfl) (by quickRfl)
    (by quickRfl) (by quickRfl) (by quickRfl) CFSG.KD.M24S2.sW0 (by quickRfl) (by quickRfl)
    CFSG.KD.M24S2.sC0 (by quickRfl)
  have s2 := lceOk_sound h2 h' fun r hr => by
    change r < 29 at hr
    have hs : ∀ r < 29, subRel relMap (CFSG.KD.M24B.selRT r) (CFSG.KD.M24S2.selRT r) = true := by
      intro r hr
      interval_cases r <;> quickRfl
    exact rename h hrels hr (hs r hr)
  have e2 : (fun j => bval h' (wWord (CFSG.KD.M24S2.selST j)) (wLen (CFSG.KD.M24S2.selST j))) ''
      {j | j < nat_lit 4} = h' '' {g | 2 * g < nat_lit 8} :=
    image_one h' (n := 4) (by norm_num) fun j hj => by
      interval_cases j <;> exact Nat.eq_of_beq_eq_true (by quickRfl)
  set x : G := (h' 1)⁻¹ * h' 0 with hx
  have eST : bval h' (wWord (CFSG.KD.M24S1.selST 0)) (wLen (CFSG.KD.M24S1.selST 0)) = x := by
    have hL : wLen (CFSG.KD.M24S1.selST 0) = [3, 0].length :=
      Nat.eq_of_beq_eq_true (by quickRfl)
    rw [hL, bval_list h' _ [3, 0] fun q hq => by
      change q < 2 at hq
      interval_cases q <;> exact Nat.eq_of_beq_eq_true (by quickRfl)]
    rw [hx]
    simp [letV]
  have hpow : x ^ 5 = 1 := by
    have h4 := hr1 4 (by norm_num)
    have hL : wLen (CFSG.KD.M24S1.selRT 4) = [3, 0, 3, 0, 3, 0, 3, 0, 3, 0].length :=
      Nat.eq_of_beq_eq_true (by quickRfl)
    rw [hL, bval_list h' _ [3, 0, 3, 0, 3, 0, 3, 0, 3, 0] fun q hq => by
      change q < 10 at hq
      interval_cases q <;> exact Nat.eq_of_beq_eq_true (by quickRfl)] at h4
    rw [← h4, hx]
    simp [letV, pow_succ, mul_assoc]
  have e1 : Subgroup.closure ((fun j => bval h' (wWord (CFSG.KD.M24S1.selST j))
      (wLen (CFSG.KD.M24S1.selST j))) '' {j | j < nat_lit 1}) = Subgroup.zpowers x := by
    have e0 : {j : ℕ | j < nat_lit 1} = {0} := by
      ext j
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
      omega
    rw [e0, Set.image_singleton, eST, ← Subgroup.zpowers_eq_closure]
  rw [e1] at s1
  rw [e2] at s2
  have hord : orderOf x ∣ 5 := orderOf_dvd_of_pow_eq_one hpow
  have c0 : Nat.card (Subgroup.zpowers x) ≠ 0 ∧ Nat.card (Subgroup.zpowers x) ≤ 5 := by
    rw [Nat.card_zpowers]
    exact ⟨(Nat.pos_of_dvd_of_pos hord (by norm_num)).ne', Nat.le_of_dvd (by norm_num) hord⟩
  have m1 : Subgroup.zpowers x ≤ Subgroup.closure (h' '' {g | 2 * g < nat_lit 8}) := by
    rw [Subgroup.zpowers_le]
    have a0 : h' 0 ∈ Subgroup.closure (h' '' {g | 2 * g < nat_lit 8}) :=
      Subgroup.subset_closure ⟨0, by change 2 * 0 < 8; omega, rfl⟩
    have a1 : h' 1 ∈ Subgroup.closure (h' '' {g | 2 * g < nat_lit 8}) :=
      Subgroup.subset_closure ⟨1, by change 2 * 1 < 8; omega, rfl⟩
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ a1) a0
  have m2 : Subgroup.closure (h' '' {g | 2 * g < nat_lit 8}) ≤
      Subgroup.closure (h' '' {g | 2 * g < nat_lit 14}) := by
    apply Subgroup.closure_mono
    rintro _ ⟨g, hg, rfl⟩
    exact ⟨g, by change 2 * g < 8 at hg; change 2 * g < 14; omega, rfl⟩
  have c1 := KB.card_le_step ⟨m1, s1.1, s1.2⟩ c0
  have c2 := KB.card_le_step ⟨m2, s2.1, s2.2⟩ c1
  have e3 : h' '' {g | 2 * g < nat_lit 14} = h '' {i | i < 7} := by
    ext y
    simp only [Set.mem_image, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨g, hg, rfl⟩
      change 2 * g < 14 at hg
      refine ⟨ord g, ?_, rfl⟩
      have hg7 : g < 7 := by omega
      interval_cases g <;> decide
    · rintro ⟨i, hi, rfl⟩
      have pos : ∀ i < 7, ∃ g, 2 * g < 14 ∧ ord g = i := by
        intro i hi
        interval_cases i
        exacts [⟨4, by decide, rfl⟩, ⟨5, by decide, rfl⟩, ⟨0, by decide, rfl⟩, ⟨1, by decide, rfl⟩,
          ⟨6, by decide, rfl⟩, ⟨2, by decide, rfl⟩, ⟨3, by decide, rfl⟩]
      obtain ⟨g, hg, e⟩ := pos i hi
      exact ⟨g, hg, by rw [h'_def]; simp only [e]⟩
  rw [e3] at c2
  exact c2

end CertificateChecks.KernelBounds.M24C

end
