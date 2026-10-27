module

public import Certificates.Kernel.Fi23S.Fact1014
public import Certificates.Kernel.Fi23Sq.ChkDefs
public import Certificates.Kernel.Fi23Q.Regs
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.SqReduce

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi23Sq

open CFSG.KC.Enum CFSG.KC.Fi23K CFSG.KC.Fi23R CFSG.KC.Fi23S CFSG.KD.Fi23K CFSG.KD.Fi23S
  CFSG.KD.Fi23Sq CFSG.KS.PEnum CFSG.KS.Raw.Orb CFSG.F3.Native CFSG.Sporadic.Fi23
  CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native CFSG.Sporadic.Fi23.Native
  CertificateChecks.KernelFi23S CertificateChecks.KernelFi23Q CFSG.EvenSporadicStandard.TwoFi22
open CFSG.Sporadic.Th hiding J a b closure_ab gA gB rows_B_cube

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem conj_odd24650 {X : Type*} [Group X] {s r δ : X} (hs : s ^ 2 = 1) (hr : r ^ 2 = 1)
    {m : ℕ} (hm : m % 2 = 1) (h : (s * r) ^ m = 1) (hsδ : s * δ = δ * s) (hrδ : r * δ = δ * r) :
    ∃ u : X, u * δ = δ * u ∧ u * r * u⁻¹ = s := by
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
  have hc : Commute (s * r) δ := Commute.mul_left hsδ hrδ
  refine ⟨(s * r) ^ (k + 1), (hc.pow_left (k + 1)).eq, ?_⟩
  have e : k + 1 + (k + 1) = 2 * k + 1 + 1 := by ring
  rw [mul_assoc, ← inv_pow, h2, ← mul_assoc, ← pow_add, e, pow_succ, h, one_mul, mul_assoc, hr2,
    mul_one]

theorem inv_comm24650 {X : Type*} [Group X] {u δ : X} (h : u * δ = δ * u) :
    u⁻¹ * δ = δ * u⁻¹ := by
  calc u⁻¹ * δ = u⁻¹ * (δ * u) * u⁻¹ := by group
    _ = u⁻¹ * (u * δ) * u⁻¹ := by rw [h]
    _ = δ * u⁻¹ := by group

theorem card_centralizer_conj24650 {X : Type*} [Group X] (δ g : X) :
    Nat.card (Subgroup.centralizer ({g * δ * g⁻¹} : Set X)) =
      Nat.card (Subgroup.centralizer ({δ} : Set X)) := by
  have e : Subgroup.centralizer ({g * δ * g⁻¹} : Set X) =
      (Subgroup.centralizer ({δ} : Set X)).map (MulAut.conj g).toMonoidHom := by
    ext x
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_map]
    constructor
    · intro h
      refine ⟨g⁻¹ * x * g, Subgroup.mem_centralizer_singleton_iff.2 ?_, by
        simp [MulAut.conj_apply, mul_assoc]⟩
      calc g⁻¹ * x * g * δ = g⁻¹ * (x * (g * δ * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * δ * g⁻¹) * x) * g := by rw [h]
        _ = δ * (g⁻¹ * x * g) := by group
    · rintro ⟨y, hy, rfl⟩
      have hy' := Subgroup.mem_centralizer_singleton_iff.1 hy
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      calc g * y * g⁻¹ * (g * δ * g⁻¹) = g * (y * δ) * g⁻¹ := by group
        _ = g * (δ * y) * g⁻¹ := by rw [hy']
        _ = g * δ * g⁻¹ * (g * y * g⁻¹) := by group
  rw [e]
  exact Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem misc_parts24650 (h : miscSq = true) : (∀ q < 6, tA G 2776 q = d0 q) ∧
    (∀ l < 42, tb H l 2776 = 2776) ∧ ∀ f < 35, famF f = true := by
  unfold miscSq d0Ok at h
  rw [bAnd_eq, bAnd_eq, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨fun q hq => Nat.eq_of_beq_eq_true (allN_iff.1 h1 q hq),
    fun l hl => Nat.eq_of_beq_eq_true (allN_iff.1 h2 l hl), fun f hf => allN_iff.1 h3 f hf⟩

theorem lfSq_spec24650 {k j : ℕ} (h : lfSq k j = true) : ∃ q < 6, gK k j (gK k j q) ≠ d0 q ∧
    lfT (Nat.land (Nat.shiftRight (cA k j) 3) 7) (Nat.shiftRight (cA k j) 6) (cB k j) k j = true := by
  unfold lfSq lfC at h
  rw [strictB_eq, strictB_eq, bAnd_eq, bAnd_eq, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨_, Nat.blt_eq.mp h1, fun e => ?_, h3⟩
  rw [e, Nat.beq_refl] at h2
  exact absurd h2 (by decide)

theorem lfT_spec24650 {t p u k j : ℕ} (h : lfT t p u k j = true) :
    (t = 0 ∧ code k j < 2) ∨ (t = 1 ∧ 110 ≤ code k j) ∨
    (t = 2 ∧ p < 262144 ∧ 110 ≤ code (Nat.shiftRight p 9) (Nat.land p 511) ∧
      ∀ b < 6, gP p (gK k j b) = d0 b) ∨
    (t = 3 ∧ p < 35 ∧ ∀ q < 6, cyK (hF k j p) q 119 1 (hF k j p q) % 2 = 1) ∨
    (t = 4 ∧ p < 262144 ∧ u < 262144 ∧
      Nat.land (Nat.shiftRight (cA (Nat.shiftRight p 9) (Nat.land p 511)) 3) 7 = 3 ∧
      ∀ b < 6, gK k j (gP u b) = gP u (gP p b)) := by
  unfold lfT at h
  rw [bIf_eq] at h
  split_ifs at h with h0
  · exact Or.inl ⟨Nat.eq_of_beq_eq_true h0, Nat.blt_eq.mp h⟩
  rw [bIf_eq] at h
  split_ifs at h with h1
  · exact Or.inr (Or.inl ⟨Nat.eq_of_beq_eq_true h1, Nat.ble_eq.mp h⟩)
  rw [bIf_eq] at h
  split_ifs at h with h2
  · rw [bAnd_eq, bAnd_eq, Bool.and_eq_true, Bool.and_eq_true] at h
    obtain ⟨a1, a2, a3⟩ := h
    exact Or.inr (Or.inr (Or.inl ⟨Nat.eq_of_beq_eq_true h2, Nat.blt_eq.mp a1, Nat.ble_eq.mp a2,
      fun b hb => Nat.eq_of_beq_eq_true (allN_iff.1 a3 b hb)⟩))
  rw [bIf_eq] at h
  split_ifs at h with h3
  · rw [bAnd_eq, Bool.and_eq_true] at h
    obtain ⟨a1, a2⟩ := h
    refine Or.inr (Or.inr (Or.inr (Or.inl ⟨Nat.eq_of_beq_eq_true h3, Nat.blt_eq.mp a1,
      fun q hq => ?_⟩)))
    have a := allN_iff.1 a2 q hq
    rw [strictB_eq] at a
    have a' := Nat.eq_of_beq_eq_true a
    change _ &&& 1 = 1 at a'
    rw [Nat.and_one_is_mod] at a'
    exact a'
  rw [bIf_eq] at h
  split_ifs at h with h4
  · rw [bAnd_eq, bAnd_eq, bAnd_eq, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
    obtain ⟨a1, a2, a3, a4⟩ := h
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨Nat.eq_of_beq_eq_true h4, Nat.blt_eq.mp a1,
      Nat.blt_eq.mp a2, Nat.eq_of_beq_eq_true a3,
      fun b hb => Nat.eq_of_beq_eq_true (allN_iff.1 a4 b hb)⟩)))

theorem words_lt24650 : ∀ w : List ℕ, List.rec (motive := fun _ => Bool) true
    (fun z _ ih => bAnd(Nat.blt z (nat_lit 24), ih)) w = true → ∀ z ∈ w, z < 24
  | [], _, _, hz => absurd hz List.not_mem_nil
  | z :: w, h, x, hx => by
    change bAnd(Nat.blt z (nat_lit 24), List.rec (motive := fun _ => Bool) true
      (fun z _ ih => bAnd(Nat.blt z (nat_lit 24), ih)) w) = true at h
    rw [bAnd_eq, Bool.and_eq_true] at h
    rcases List.mem_cons.1 hx with rfl | hx
    · exact Nat.blt_eq.mp h.1
    · exact words_lt24650 w h.2 x hx

theorem idx_lt512 {p : ℕ} (hp : p < 262144) : Nat.shiftRight p 9 < 512 ∧ Nat.land p 511 < 512 := by
  refine ⟨?_, lt_of_le_of_lt Nat.and_le_right (by norm_num)⟩
  have e : Nat.shiftRight p 9 = p / 512 := by
    change p >>> 9 = _
    rw [Nat.shiftRight_eq_div_pow]
  rw [e]
  omega

section


noncomputable def sL24650 (k j : ℕ) : CFSG.Sporadic.Fi23.J :=
  treeG CFSG.Sporadic.Fi23.TS[0]! (pairG sylG) k * treeG CFSG.Sporadic.Fi23.TS[1]! (pairG sylG) j

theorem eq_of_base24650 {x y : CFSG.Sporadic.Fi23.J} (h : ∀ q < 6, idx 31671 x q = idx 31671 y q) : x = y := by
  have h1 : y⁻¹ * x = 1 := by
    apply sep
    intro t ht
    have hs : chainQ.size = 6 := rfl
    rw [hs] at ht
    have e : chainQ[t]! = t := by
      interval_cases t <;> rfl
    rw [e, idx_mul, h t ht, idx_inv_idx]
  rw [inv_mul_eq_one] at h1
  exact h1.symm

theorem tabS_eq24650 (i : ℕ) : tabS i = treeTabs 31671
    (chainTrees 31671 (sylLetters (chainLetters orbLit)) sylBase)[i]!
      (sylLetters (chainLetters orbLit)) :=
  congrArg (fun O => treeTabs 31671 (chainTrees 31671 (sylLetters (chainLetters O)) sylBase)[i]!
    (sylLetters (chainLetters O))) orb_eq

theorem leaf_idx24650 {k j : ℕ} (hk : k < 512) (hj : j < 512) :
    ∀ y < 31671, idx 31671 (sL24650 k j) y = gK k j y := by
  intro y hy
  have h0 := rep_tabS (i := 0) (by rw [sylBase_size]; norm_num) (k := k)
    (by rw [TS_size (l := 0) rfl]; exact hk)
  have h1 := rep_tabS (i := 1) (by rw [sylBase_size]; norm_num) (k := j)
    (by rw [TS_size (l := 1) rfl]; exact hj)
  rw [tabS_eq24650] at h0 h1
  exact ((Rep.compT h0 h1) y hy).symm.trans (leaf_ap hk hj hy)

theorem rep_leaf24650 {k j : ℕ} (hk : k < 512) (hj : j < 512) :
    Rep 31671 (compT 31671 t0[k]! t1[j]!) (sL24650 k j) :=
  fun y hy => (leaf_ap hk hj hy).trans (leaf_idx24650 hk hj y hy).symm

theorem sL_mem24650 {k j : ℕ} (hk : k < 512) (hj : j < 512) : sL24650 k j ∈ slvl 0 := by
  have hT0 := syl_facts.1 0 (by rw [sylBase_size]; norm_num)
  have hT1 := syl_facts.1 1 (by rw [sylBase_size]; norm_num)
  unfold sL24650
  refine (slvl 0).mul_mem (hT0.treeG_mem (by rw [TS_size (l := 0) rfl]; exact hk)) ?_
  exact levelGroup_anti (pairG sylG) (Nat.zero_le 1)
    (hT1.treeG_mem (by rw [TS_size (l := 1) rfl]; exact hj))

theorem mem_slvl_pair24650 {g : CFSG.Sporadic.Fi23.J} (hg : g ∈ slvl 0) :
    ∃ k < 512, ∃ j < 512, g = sL24650 k j := by
  obtain ⟨k0, hk0, h, hh, rfl⟩ := exists_tree_mul (i := 0) (by rw [sylBase_size]; norm_num) hg
  obtain ⟨k1, hk1, h', hh', rfl⟩ := exists_tree_mul (i := 1) (by rw [sylBase_size]; norm_num) hh
  have hh'' : h' ∈ slvl 2 := hh'
  rw [slvl_two, Subgroup.mem_bot] at hh''
  rw [TS_size (l := 0) rfl] at hk0
  rw [TS_size (l := 1) rfl] at hk1
  refine ⟨k0, hk0, k1, hk1, ?_⟩
  rw [hh'', mul_one]
  rfl

theorem d0_idx24650 (hm : miscSq = true) {q : ℕ} (hq : q < 6) :
    idx 31671 (conjPt 2776) q = d0 q := by
  rw [conjPt_acts (by norm_num) q (by omega)]
  exact (misc_parts24650 hm).1 q hq

theorem d0_sq24650 : conjPt 2776 * conjPt 2776 = 1 := by
  rw [← pow_two]
  exact conjPt_sq (by norm_num)

theorem LS_fix24650 (hm : miscSq = true) {l : ℕ} (hl : l < CFSG.Sporadic.Fi23.LS.size) :
    ap CFSG.Sporadic.Fi23.LS[l]! 2776 = 2776 := by
  have e : CFSG.Sporadic.Fi23.LS = sylLetters (chainLetters orbLit) :=
    congrArg (fun O => sylLetters (chainLetters O)) orb_eq
  rw [e] at hl ⊢
  rw [syl_TR.1] at hl
  rw [((syl_TR.2 l hl).2 2776 (by norm_num)).1]
  exact (misc_parts24650 hm).2.1 l hl

theorem fix_of_mem24650 (hm : miscSq = true) {g : CFSG.Sporadic.Fi23.J} (hg : g ∈ slvl 0) :
    idx 31671 g 2776 = 2776 := by
  unfold slvl levelGroup lettersGroup at hg
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨l, hl, rfl⟩ := hx
    have hl' : l < CFSG.Sporadic.Fi23.LS.size := mem_levelLetters_zero.1 hl
    rw [← rep_LS_all l hl' 2776 (by norm_num)]
    exact LS_fix24650 hm hl'
  | one => exact idx_one _
  | mul x y _ _ hx hy => rw [idx_mul, hy, hx]
  | inv x _ hx =>
    calc idx 31671 x⁻¹ 2776 = idx 31671 x⁻¹ (idx 31671 x 2776) := by rw [hx]
      _ = 2776 := idx_inv_idx x 2776

theorem commute_of_fix24650 {g : CFSG.Sporadic.Fi23.J} (h : idx 31671 g 2776 = 2776) :
    g * conjPt 2776 = conjPt 2776 * g := by
  have e := (CFSG.Sporadic.Fi23.idx_eq_iff (by norm_num) (by norm_num)).1 h
  calc g * conjPt 2776 = g * conjPt 2776 * g⁻¹ * g := by rw [inv_mul_cancel_right]
    _ = conjPt 2776 * g := by rw [e]

theorem slvl_commute24650 (hm : miscSq = true) {g : CFSG.Sporadic.Fi23.J} (hg : g ∈ slvl 0) :
    g * conjPt 2776 = conjPt 2776 * g :=
  commute_of_fix24650 (fix_of_mem24650 hm hg)

theorem odd_order24650 {h : CFSG.Sporadic.Fi23.J} {H : ℕ → ℕ} (hH : ∀ y < 31671, idx 31671 h y = H y)
    (hc : ∀ q < 6, cyK H q 119 1 (H q) % 2 = 1) : ∃ m, m % 2 = 1 ∧ h ^ m = 1 := by
  have hrep : ∀ n, ∀ x < 31671, Nat.repeat H n x = idx 31671 (h ^ n) x := by
    intro n
    induction n with
    | zero => intro x _; rw [pow_zero, idx_one]; rfl
    | succ n ih =>
      intro x hx
      change H (Nat.repeat H n x) = _
      rw [pow_succ', idx_mul, ← ih x hx, hH _ (by rw [ih x hx]; exact idx_lt _ hx)]
  have hfix : ∀ q < 6, Nat.repeat H (cyK H q 119 1 (H q)) q = q := by
    intro q hq
    have h1 := hc q hq
    obtain ⟨hle, hr⟩ := cyK_spec H q 119 1 (H q) _ rfl (by omega)
    generalize cyK H q 119 1 (H q) = c at hle hr h1 ⊢
    have e : c = (c - 1) + 1 := by omega
    rw [e, repeat_add]
    exact hr
  have hall : ∀ q ∈ List.range 6, cyK H q 119 1 (H q) % 2 = 1 := fun q hq =>
    hc q (List.mem_range.1 hq)
  refine ⟨(List.range 6).foldl (fun L q => L.lcm (cyK H q 119 1 (H q))) 1,
    foldl_odd _ _ 1 rfl hall, eq_of_base24650 fun q hq => ?_⟩
  rw [idx_one, ← hrep _ q (by omega)]
  exact repeat_dvd _ (hfix q hq)
    ((foldl_dvd (fun q => cyK H q 119 1 (H q)) (List.range 6) 1).2 q (List.mem_range.2 hq))

theorem mem_D23_of_code24650 {k j : ℕ} (hk : k < 512) (hj : j < 512) (hc : 110 ≤ code k j)
    (hs2 : sL24650 k j ^ 2 = 1) : sL24650 k j ∈ D23 := by
  obtain ⟨hr, hcyc⟩ := lf14_cases (lf14_all hk hj) (by omega)
  have h27 : 27 ≤ (code k j - 2) / 4 := by omega
  obtain ⟨-, -, uA⟩ := UR_eq
  obtain ⟨-, -, wA⟩ := wordsABC_ok
  have e : (code k j - 2) / 4 = 27 + ((code k j - 2) / 4 - 27) := by omega
  have hi : (code k j - 2) / 4 - 27 < 2 := by omega
  have hu := uA _ hi
  rw [← e] at hu
  have ho := rep_odd (X := dTab orbLit) (ws := wordsA) (i := (code k j - 2) / 4 - 27) hk hj hi
    (wA _ hi) (fun y hy => by rw [xEv_A h27]; exact D_ap hy) hu hcyc
  have hmemL : (conjsOf orbLit (dTab orbLit) wordsA)[(code k j - 2) / 4 - 27]! ∈
      conjsOf orbLit (dTab orbLit) wordsA := by
    rw [getElem!_pos _ _ (by rw [conjsOf_size]; exact hi)]
    exact Array.getElem_mem _
  have hinv := Array.all_eq_true'.1 (invOK_all (dTab orbLit) wordsA fun i hi => wA i hi) _ hmemL
  have hmem : (conjsOf orbLit (dTab orbLit) wordsA)[(code k j - 2) / 4 - 27]! ∈
      conjsOf orb (dTab orb) wordsA := by
    rw [orb_eq]
    exact hmemL
  obtain ⟨w, hw⟩ := rep_conjsOf rep_dTab hmem hinv
  have hcj := isConj_of_oddOK (rep_leaf24650 hk hj) hw hs2
    (by rw [conj_pow, d_sq', mul_one, mul_inv_cancel]) ho
  exact (isConj_iff.2 ⟨w, rfl⟩).trans hcj

theorem t2_mem24650 (hm : miscSq = true) {k j p : ℕ} (hk : k < 512) (hj : j < 512)
    (hp : p < 262144) (hc : 110 ≤ code (Nat.shiftRight p 9) (Nat.land p 511))
    (hb : ∀ b < 6, gP p (gK k j b) = d0 b) (hs2 : sL24650 k j * sL24650 k j = 1) :
    conjPt 2776 * sL24650 k j ∈ D23 := by
  obtain ⟨hk', hj'⟩ := idx_lt512 hp
  have he : sL24650 (Nat.shiftRight p 9) (Nat.land p 511) * sL24650 k j = conjPt 2776 :=
    eq_of_base24650 fun q hq => by
      have hq' : q < 31671 := by omega
      rw [idx_mul, leaf_idx24650 hk hj q hq',
        leaf_idx24650 hk' hj' (gK k j q) (gK_lt hk hj hq'), d0_idx24650 hm hq]
      exact hb q hq
  have hd : conjPt 2776 * sL24650 k j = sL24650 (Nat.shiftRight p 9) (Nat.land p 511) := by
    rw [← he, mul_assoc, hs2, mul_one]
  rw [hd]
  refine mem_D23_of_code24650 hk' hj' hc ?_
  have hcomm := slvl_commute24650 hm (sL_mem24650 hk hj)
  rw [← hd, pow_two]
  calc conjPt 2776 * sL24650 k j * (conjPt 2776 * sL24650 k j)
      = conjPt 2776 * (sL24650 k j * conjPt 2776) * sL24650 k j := by group
    _ = conjPt 2776 * (conjPt 2776 * sL24650 k j) * sL24650 k j := by rw [hcomm]
    _ = (conjPt 2776 * conjPt 2776) * (sL24650 k j * sL24650 k j) := by group
    _ = 1 := by rw [d0_sq24650, hs2, one_mul]

theorem wz_idx24650 : ∀ w : List ℕ, (∀ z ∈ w, z < 24) → ∀ x < 31671,
    wz w x = idx 31671 (w.map (pairG gs)).prod x ∧
      wzi w x = idx 31671 (w.map (pairG gs)).prod⁻¹ x
  | [], _, x, _ => by
    refine ⟨?_, ?_⟩ <;> simp only [List.map_nil, List.prod_nil, inv_one, idx_one] <;> rfl
  | z :: w, hw, x, hx => by
    have hz : z < 24 := hw z List.mem_cons_self
    have hw' : ∀ y ∈ w, y < 24 := fun y hy => hw y (List.mem_cons_of_mem z hy)
    have hx1 : Nat.xor z 1 = CFSG.Perm.Native.invL z := by
      interval_cases z <;> rfl
    have hz1 : Nat.xor z 1 < 24 := by
      rw [hx1]
      unfold CFSG.Perm.Native.invL
      split_ifs <;> omega
    refine ⟨?_, ?_⟩
    · change tb G (Nat.add (nat_lit 52) z) (wz w x) = _
      rw [(wz_idx24650 w hw' x hx).1, List.map_cons, List.prod_cons, idx_mul]
      exact (letter_acts hz _ (idx_lt _ hx)).symm
    · change strictN (tb G (Nat.add (nat_lit 52) (Nat.xor z (nat_lit 1))) x) (fun y => wzi w y) = _
      have e1 : tb G (Nat.add (nat_lit 52) (Nat.xor z (nat_lit 1))) x =
          idx 31671 (pairG gs z)⁻¹ x := by
        rw [← pairG_invL, ← hx1]
        exact (letter_acts hz1 x hx).symm
      rw [strictN_eq, e1, (wz_idx24650 w hw' _ (idx_lt _ hx)).2, List.map_cons, List.prod_cons,
        mul_inv_rev, idx_mul]

theorem fam_rep24650 {a b : ℕ} {w : List ℕ} (h : famE a b w = true) :
    ∃ ρ : CFSG.Sporadic.Fi23.J, ρ * conjPt 2776 = conjPt 2776 * ρ ∧ (ρ * ρ) ^ 2 = 1 ∧
      ∀ y < 31671, idx 31671 (ρ * ρ) y = rW a b w y := by
  unfold famE at h
  rw [bAnd_eq, bAnd_eq, bAnd_eq, bAnd_eq, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
    Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have ha : a < 512 := Nat.blt_eq.mp h1
  have hb : b < 512 := Nat.blt_eq.mp h2
  have hw : ∀ z ∈ w, z < 24 := words_lt24650 w h3
  have hW := wz_idx24650 w hw
  have hρ : ∀ y < 31671, idx 31671 ((w.map (pairG gs)).prod * sL24650 a b *
      ((w.map (pairG gs)).prod)⁻¹) y = rhoW a b w y := by
    intro y hy
    change _ = wz w (gK a b (wzi w y))
    have l1 := idx_lt ((w.map (pairG gs)).prod)⁻¹ hy
    rw [(hW y hy).2, ← leaf_idx24650 ha hb _ l1, (hW _ (idx_lt _ l1)).1]
    simp only [idx_mul]
  have hρρ : ∀ y < 31671, idx 31671 ((w.map (pairG gs)).prod * sL24650 a b *
      ((w.map (pairG gs)).prod)⁻¹ * ((w.map (pairG gs)).prod * sL24650 a b *
      ((w.map (pairG gs)).prod)⁻¹)) y = rW a b w y := by
    intro y hy
    change _ = wz w (gK a b (gK a b (wzi w y)))
    have l1 := idx_lt ((w.map (pairG gs)).prod)⁻¹ hy
    have l2 := idx_lt (sL24650 a b) l1
    have e : (w.map (pairG gs)).prod * sL24650 a b * ((w.map (pairG gs)).prod)⁻¹ *
        ((w.map (pairG gs)).prod * sL24650 a b * ((w.map (pairG gs)).prod)⁻¹) =
        (w.map (pairG gs)).prod * sL24650 a b * sL24650 a b * ((w.map (pairG gs)).prod)⁻¹ := by
      group
    rw [(hW y hy).2, ← leaf_idx24650 ha hb _ l1, ← leaf_idx24650 ha hb _ l2,
      (hW _ (idx_lt _ l2)).1, e]
    simp only [idx_mul]
  refine ⟨_, commute_of_fix24650 ((hρ 2776 (by norm_num)).trans (Nat.eq_of_beq_eq_true h4)),
    ?_, hρρ⟩
  refine eq_of_base24650 fun q hq => ?_
  have hq' : q < 31671 := by omega
  have l1 : rW a b w q < 31671 := by rw [← hρρ q hq']; exact idx_lt _ hq'
  rw [pow_two, idx_mul, hρρ q hq', hρρ _ l1, idx_one]
  exact fixB_spec h5 q hq

theorem t3_sq24650 (hm : miscSq = true) {k j p : ℕ} (hk : k < 512) (hj : j < 512) (hp : p < 35)
    (hcyc : ∀ q < 6, cyK (hF k j p) q 119 1 (hF k j p q) % 2 = 1)
    (hs2 : sL24650 k j * sL24650 k j = 1) :
    ∃ w : CFSG.Sporadic.Fi23.J, w * conjPt 2776 = conjPt 2776 * w ∧ w * w = sL24650 k j := by
  obtain ⟨ρ, hρc, hr2, hρρ⟩ := fam_rep24650 (a := List.getD FA p 0) (b := List.getD FB p 0)
    (w := List.getD FW p []) ((misc_parts24650 hm).2.2 p hp)
  have hact : ∀ y < 31671, idx 31671 (sL24650 k j * (ρ * ρ)) y = hF k j p y := fun y hy => by
    rw [idx_mul, hρρ y hy]
    exact leaf_idx24650 hk hj _ (by rw [← hρρ y hy]; exact idx_lt _ hy)
  obtain ⟨m, hm1, hm2⟩ := odd_order24650 hact hcyc
  have hs2' : sL24650 k j ^ 2 = 1 := by rw [pow_two]; exact hs2
  have hsc := slvl_commute24650 hm (sL_mem24650 hk hj)
  have hrc : ρ * ρ * conjPt 2776 = conjPt 2776 * (ρ * ρ) := by
    rw [mul_assoc, hρc, ← mul_assoc, hρc, mul_assoc]
  obtain ⟨u, hu, hconj⟩ := conj_odd24650 hs2' hr2 hm1 hm2 hsc hrc
  refine ⟨u * ρ * u⁻¹, ?_, ?_⟩
  · have hui := inv_comm24650 hu
    calc u * ρ * u⁻¹ * conjPt 2776 = u * ρ * (u⁻¹ * conjPt 2776) := by group
      _ = u * (ρ * conjPt 2776) * u⁻¹ := by rw [hui]; group
      _ = (u * conjPt 2776) * ρ * u⁻¹ := by rw [hρc]; group
      _ = conjPt 2776 * (u * ρ * u⁻¹) := by rw [hu]; group
  · calc u * ρ * u⁻¹ * (u * ρ * u⁻¹) = u * (ρ * ρ) * u⁻¹ := by group
      _ = sL24650 k j := hconj

theorem t4_sq24650 (hm : miscSq = true) (hL : ∀ k < 512, ∀ j < 512, lfSq k j = true)
    {k j p u : ℕ} (hk : k < 512) (hj : j < 512) (hp : p < 262144) (hu : u < 262144)
    (ht : Nat.land (Nat.shiftRight (cA (Nat.shiftRight p 9) (Nat.land p 511)) 3) 7 = 3)
    (hb : ∀ b < 6, gK k j (gP u b) = gP u (gP p b)) (hs2 : sL24650 k j * sL24650 k j = 1) :
    ∃ w : CFSG.Sporadic.Fi23.J, w * conjPt 2776 = conjPt 2776 * w ∧ w * w = sL24650 k j := by
  obtain ⟨hk', hj'⟩ := idx_lt512 hp
  obtain ⟨hku, hju⟩ := idx_lt512 hu
  have he : sL24650 k j * sL24650 (Nat.shiftRight u 9) (Nat.land u 511) =
      sL24650 (Nat.shiftRight u 9) (Nat.land u 511) *
        sL24650 (Nat.shiftRight p 9) (Nat.land p 511) := eq_of_base24650 fun q hq => by
    have hq' : q < 31671 := by omega
    rw [idx_mul, idx_mul, leaf_idx24650 hku hju q hq',
      leaf_idx24650 hk hj _ (gK_lt hku hju hq'), leaf_idx24650 hk' hj' q hq',
      leaf_idx24650 hku hju _ (gK_lt hk' hj' hq')]
    exact hb q hq
  have hs' : sL24650 (Nat.shiftRight p 9) (Nat.land p 511) =
      (sL24650 (Nat.shiftRight u 9) (Nat.land u 511))⁻¹ * sL24650 k j *
        sL24650 (Nat.shiftRight u 9) (Nat.land u 511) := by
    rw [mul_assoc, he, ← mul_assoc, inv_mul_cancel, one_mul]
  have hs'2 : sL24650 (Nat.shiftRight p 9) (Nat.land p 511) *
      sL24650 (Nat.shiftRight p 9) (Nat.land p 511) = 1 := by
    rw [hs']
    calc (sL24650 (Nat.shiftRight u 9) (Nat.land u 511))⁻¹ * sL24650 k j *
          sL24650 (Nat.shiftRight u 9) (Nat.land u 511) *
        ((sL24650 (Nat.shiftRight u 9) (Nat.land u 511))⁻¹ * sL24650 k j *
          sL24650 (Nat.shiftRight u 9) (Nat.land u 511)) =
        (sL24650 (Nat.shiftRight u 9) (Nat.land u 511))⁻¹ * (sL24650 k j * sL24650 k j) *
          sL24650 (Nat.shiftRight u 9) (Nat.land u 511) := by group
      _ = 1 := by rw [hs2]; group
  obtain ⟨_, _, _, hT⟩ := lfSq_spec24650 (hL _ hk' _ hj')
  rw [ht] at hT
  rcases lfT_spec24650 hT with ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨-, hp3, hcyc⟩ | ⟨h0, -⟩
  · exact absurd h0 (by decide)
  · exact absurd h0 (by decide)
  · exact absurd h0 (by decide)
  · obtain ⟨w, hwc, hww⟩ := t3_sq24650 hm hk' hj' hp3 hcyc hs'2
    have hUc := slvl_commute24650 hm (sL_mem24650 hku hju)
    have hUi := @inv_comm24650 J inferInstance _ _ hUc
    refine ⟨sL24650 (Nat.shiftRight u 9) (Nat.land u 511) * w *
      (sL24650 (Nat.shiftRight u 9) (Nat.land u 511))⁻¹, ?_, ?_⟩
    · calc sL24650 (Nat.shiftRight u 9) (Nat.land u 511) * w *
            (sL24650 (Nat.shiftRight u 9) (Nat.land u 511))⁻¹ * conjPt 2776 =
          sL24650 (Nat.shiftRight u 9) (Nat.land u 511) * w *
            ((sL24650 (Nat.shiftRight u 9) (Nat.land u 511))⁻¹ * conjPt 2776) := by group
        _ = sL24650 (Nat.shiftRight u 9) (Nat.land u 511) * (w * conjPt 2776) *
            (sL24650 (Nat.shiftRight u 9) (Nat.land u 511))⁻¹ := by rw [hUi]; group
        _ = (sL24650 (Nat.shiftRight u 9) (Nat.land u 511) * conjPt 2776) * w *
            (sL24650 (Nat.shiftRight u 9) (Nat.land u 511))⁻¹ := by rw [hwc]; group
        _ = conjPt 2776 * (sL24650 (Nat.shiftRight u 9) (Nat.land u 511) * w *
            (sL24650 (Nat.shiftRight u 9) (Nat.land u 511))⁻¹) := by rw [hUc]; group
    · calc sL24650 (Nat.shiftRight u 9) (Nat.land u 511) * w *
            (sL24650 (Nat.shiftRight u 9) (Nat.land u 511))⁻¹ *
          (sL24650 (Nat.shiftRight u 9) (Nat.land u 511) * w *
            (sL24650 (Nat.shiftRight u 9) (Nat.land u 511))⁻¹) =
          sL24650 (Nat.shiftRight u 9) (Nat.land u 511) * (w * w) *
            (sL24650 (Nat.shiftRight u 9) (Nat.land u 511))⁻¹ := by group
        _ = sL24650 k j := by rw [hww, hs']; group
  · exact absurd h0 (by decide)

theorem sq_ne24650 (hm : miscSq = true) (hL : ∀ k < 512, ∀ j < 512, lfSq k j = true) {g : CFSG.Sporadic.Fi23.J}
    (hg : g ∈ slvl 0) : g * g ≠ conjPt 2776 := by
  obtain ⟨k, hk, j, hj, rfl⟩ := mem_slvl_pair24650 hg
  obtain ⟨q, hq, hne, -⟩ := lfSq_spec24650 (hL k hk j hj)
  intro h
  apply hne
  have hq' : q < 31671 := by omega
  rw [← leaf_idx24650 hk hj q hq', ← leaf_idx24650 hk hj _ (idx_lt _ hq'), ← idx_mul, h,
    d0_idx24650 hm hq]

theorem sq_root24650 (hm : miscSq = true) (hL : ∀ k < 512, ∀ j < 512, lfSq k j = true) {g : CFSG.Sporadic.Fi23.J}
    (hg : g ∈ slvl 0) (hg2 : g * g = 1) (hg1 : g ≠ 1) (hgD : g ∉ D23)
    (hdg : conjPt 2776 * g ∉ D23) :
    ∃ w : CFSG.Sporadic.Fi23.J, w * conjPt 2776 = conjPt 2776 * w ∧ w * w = g := by
  obtain ⟨k, hk, j, hj, rfl⟩ := mem_slvl_pair24650 hg
  obtain ⟨_, _, _, hT⟩ := lfSq_spec24650 (hL k hk j hj)
  rcases lfT_spec24650 hT with ⟨-, hc⟩ | ⟨-, hc⟩ | ⟨-, hp, hc, hb⟩ | ⟨-, hp, hcyc⟩ |
      ⟨-, hp, hu, ht, hb⟩
  · exfalso
    rcases lf13_cases (lf13_all hk hj) with ⟨-, b, hb, hne⟩ | ⟨-, hfix⟩ | ⟨h2, -⟩ | ⟨h2, -⟩
    · apply hne
      have hb' : b < 31671 := by omega
      rw [← leaf_idx24650 hk hj b hb', ← leaf_idx24650 hk hj _ (idx_lt _ hb'), ← idx_mul, hg2,
        idx_one]
    · exact hg1 (eq_of_base24650 fun q hq => by
        rw [leaf_idx24650 hk hj q (by omega), idx_one]
        exact hfix q hq)
    · omega
    · omega
  · exact absurd (mem_D23_of_code24650 hk hj hc (by rw [pow_two]; exact hg2)) hgD
  · exact absurd (t2_mem24650 hm hk hj hp hc hb hg2) hdg
  · exact t3_sq24650 hm hk hj hp hcyc hg2
  · exact t4_sq24650 hm hL hk hj hp hu ht hb hg2

theorem D23_conj_iff24650 (c x : CFSG.Sporadic.Fi23.J) : c * x * c⁻¹ ∈ D23 ↔ x ∈ D23 :=
  ⟨fun h => by
    have h1 := conj_mem_D23 c⁻¹ _ h
    have e : c⁻¹ * (c * x * c⁻¹) * c⁻¹⁻¹ = x := by group
    rwa [e] at h1, conj_mem_D23 c x⟩

theorem isConj_d0_24650 : IsConj d (conjPt 2776) :=
  (isConj_d_iff (conjPt 2776)).2 ⟨⟨2776, by norm_num⟩, rfl⟩

theorem card_centralizer_d0_24650 :
    Nat.card (Subgroup.centralizer ({conjPt 2776} : Set CFSG.Sporadic.Fi23.J)) = 129123503308800 := by
  obtain ⟨g, hg⟩ := isConj_iff.1 isConj_d0_24650
  rw [← hg, card_centralizer_conj24650, card_centralizer_d]

theorem sqStatement_d0_24650 (hm : miscSq = true) (hL : ∀ k < 512, ∀ j < 512, lfSq k j = true) :
    SqStatement D23 (conjPt 2776) := by
  have hT : Nat.card (slvl 0) = 2 ^ 18 := by rw [card_slvl_zero]; norm_num
  have hN : Nat.card (Subgroup.centralizer ({conjPt 2776} : Set J)) = 2 ^ 18 * 492567075 := by
    rw [card_centralizer_d0_24650]; norm_num
  have hm' : ¬ 2 ∣ 492567075 := by norm_num
  exact @sqStatement_of_sylow J inferInstance inferInstance D23 D23_conj_iff24650 (conjPt 2776)
    d0_sq24650 (slvl 0) (fun g hg => slvl_commute24650 hm hg) 18 492567075 hT hN hm'
    (fun g hg => sq_ne24650 hm hL hg)
    (fun g hg h1 h2 _ h4 h5 => sq_root24650 hm hL hg h1 h2 h4 h5)

theorem sqStatement24650_of (hm : miscSq = true) (hL : ∀ k < 512, ∀ j < 512, lfSq k j = true) :
    SqStatement D23 d := by
  obtain ⟨g, hg⟩ := isConj_iff.1 isConj_d0_24650
  have h : SqStatement D23 (g * d * g⁻¹) := by rw [hg]; exact sqStatement_d0_24650 hm hL
  exact @SqStatement.of_conj J inferInstance D23 D23_conj_iff24650 d g h

end

end CertificateChecks.KernelFi23Sq

end
