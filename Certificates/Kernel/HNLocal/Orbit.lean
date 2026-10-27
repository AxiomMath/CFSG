module

public import Certificates.Kernel.HNLocal.Fix
public import Certificates.Kernel.HNLocal.XData
public import Certificates.Kernel.HNLocal.TreeData
public import Certificates.Kernel.HNLocal.SortData
import Certificates.Kernel.HNLocal.Checks.K
import Certificates.Kernel.HNLocal.Checks.Tree0
import Certificates.Kernel.HNLocal.Checks.Tree1
import Certificates.Kernel.HNLocal.Checks.Tree2
import Certificates.Kernel.HNLocal.Checks.Tree3
import Certificates.Kernel.HNLocal.Checks.Tree4
import Certificates.Kernel.HNLocal.Checks.Tree5
import Certificates.Kernel.HNLocal.Checks.Tree6
import Certificates.Kernel.HNLocal.Checks.Tree7
import Certificates.Kernel.HNLocal.Checks.Tree8
import Certificates.Kernel.HNLocal.Checks.Tree9
import Certificates.Kernel.HNLocal.Checks.Tree10
import Certificates.Kernel.HNLocal.Checks.Tree11
import Certificates.Kernel.HNLocal.Checks.Tree12
import Certificates.Kernel.HNLocal.Checks.Tree13
import Certificates.Kernel.HNLocal.Checks.Tree14
import Certificates.Kernel.HNLocal.Checks.Tree15
import Certificates.Kernel.HNLocal.Checks.Sort0
import Certificates.Kernel.HNLocal.Checks.Sort1
import Certificates.Kernel.HNLocal.Checks.Sort2
import Certificates.Kernel.HNLocal.Checks.Sort3
import CFSG.Certificates.Kernel.J4Hub.BlockSound
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
import CFSG.Certificates.Kernel.Fam.Lin
import CFSG.Open.Defs

set_option maxRecDepth 400000
set_option exponentiation.threshold 120000

public section

namespace CertificateChecks.KernelHNLocal

open CFSG.KC.Ord CFSG.KS.Ord CFSG.KC.HNLocal CFSG.KD.HNLocal CFSG.Sporadic.F5
open CFSG.Sporadic.HN.LocalK
open scoped Matrix

local notation "Dt" => CFSG.Sporadic.HN.Native.hnData

local notation "TL" => treeLeaf XC TD MSF 1140000 M CFSG.KD.OrdHN.L CFSG.KD.OrdHN.H CM3
  CFSG.KD.OrdHN.RM GA GB GFC

@[expose] noncomputable def Xk (k : ℕ) : Vec Dt := CFSG.KS.HNLocal.cvec (recX XC M k)

theorem treeSum_eq (lo : ℕ) : ∀ n, treeSum XC TD MSF 1140000 M CFSG.KD.OrdHN.L CFSG.KD.OrdHN.H CM3
    CFSG.KD.OrdHN.RM GA GB GFC lo n = ∑ i ∈ Finset.range n, TL (lo + i)
  | 0 => rfl
  | n + 1 => by
    change CFSG.KC.Loop.strictN (treeSum XC TD MSF 1140000 M CFSG.KD.OrdHN.L CFSG.KD.OrdHN.H CM3
      CFSG.KD.OrdHN.RM GA GB GFC lo n) (fun a => Nat.add a (TL (Nat.add lo n))) = _
    rw [CFSG.KS.J4Hub.strictN_eq', treeSum_eq lo n, Finset.sum_range_succ]
    rfl

theorem sum_of {lo n v : ℕ} (h : Nat.beq (treeSum XC TD MSF 1140000 M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC lo n) v = true) :
    ∑ i ∈ Finset.range n, TL (lo + i) = v := by
  rw [← treeSum_eq]
  exact Nat.eq_of_beq_eq_true h

theorem sum_of' {N lo n v lo' n' v' : ℕ} (h : Nat.beq (treeSum XC TD MSF N M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC lo n) v = true) (hN : N = 1140000)
    (h1 : lo = lo') (h2 : n = n') (h3 : v = v') : ∑ i ∈ Finset.range n', TL (lo' + i) = v' := by
  subst hN h1 h2 h3
  exact sum_of h

theorem module_sum (m : ℕ) (hm : m < 16) :
    ∑ i ∈ Finset.range (if m < 15 then 536 else 532), TL (536 * m + i) =
      [889192975, 1056965156, 788529692, 1073742404, 1476395581, 939524664, 721420842, 905970165,
        771752472, 738198064, 754975253, 654311990, 637534748, 654312017, 704643643,
        654311934][m]! := by
  interval_cases m
  · exact sum_of' tr0 rfl (by decide) (by decide) (by decide)
  · exact sum_of' tr1 rfl (by decide) (by decide) (by decide)
  · exact sum_of' tr2 rfl (by decide) (by decide) (by decide)
  · exact sum_of' tr3 rfl (by decide) (by decide) (by decide)
  · exact sum_of' tr4 rfl (by decide) (by decide) (by decide)
  · exact sum_of' tr5 rfl (by decide) (by decide) (by decide)
  · exact sum_of' tr6 rfl (by decide) (by decide) (by decide)
  · exact sum_of' tr7 rfl (by decide) (by decide) (by decide)
  · exact sum_of' tr8 rfl (by decide) (by decide) (by decide)
  · exact sum_of' tr9 rfl (by decide) (by decide) (by decide)
  · exact sum_of' tr10 rfl (by decide) (by decide) (by decide)
  · exact sum_of' tr11 rfl (by decide) (by decide) (by decide)
  · exact sum_of' tr12 rfl (by decide) (by decide) (by decide)
  · exact sum_of' tr13 rfl (by decide) (by decide) (by decide)
  · exact sum_of' tr14 rfl (by decide) (by decide) (by decide)
  · exact sum_of' tr15 rfl (by decide) (by decide) (by decide)

theorem leaf_lt (j : ℕ) (hj : j < 8572) : TL j < 2 ^ 50 := by
  have hm : j / 536 < 16 := by omega
  have h := module_sum (j / 536) hm
  have hi : j % 536 < (if j / 536 < 15 then 536 else 532) := by split_ifs <;> omega
  have hle := Finset.single_le_sum (f := fun i => TL (536 * (j / 536) + i))
    (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 hi)
  rw [h] at hle
  have e : 536 * (j / 536) + j % 536 = j := by omega
  rw [e] at hle
  have hv : ∀ m < 16, [889192975, 1056965156, 788529692, 1073742404, 1476395581, 939524664,
      721420842, 905970165, 771752472, 738198064, 754975253, 654311990, 637534748, 654312017,
      704643643, 654311934][m]! < 2 ^ 50 := by decide
  exact lt_of_le_of_lt hle (hv _ hm)

theorem leaves_sum : ∑ j ∈ Finset.range 8572, TL j = 8800 + 2 ^ 24 * 800 := by
  have key : ∀ m ≤ 15, ∑ j ∈ Finset.range (536 * m), TL j =
      ∑ m' ∈ Finset.range m, [889192975, 1056965156, 788529692, 1073742404, 1476395581, 939524664,
        721420842, 905970165, 771752472, 738198064, 754975253, 654311990, 637534748, 654312017,
        704643643, 654311934][m']! := by
    intro m hm
    induction m with
    | zero => simp
    | succ m ih =>
      have hs := module_sum m (by omega)
      rw [if_pos (by omega)] at hs
      have e : 536 * (m + 1) = 536 * m + 536 := by ring
      rw [e, Finset.sum_range_add, ih (by omega), hs, Finset.sum_range_succ]
  have h15 := key 15 le_rfl
  have hlast := module_sum 15 (by norm_num)
  rw [if_neg (by norm_num)] at hlast
  have e : (8572 : ℕ) = 536 * 15 + 532 := by norm_num
  rw [e, Finset.sum_range_add, h15, hlast]
  decide +kernel

theorem canon_LC : Canon 5 133 13 LC := canon_of_valid v_LC

theorem cGFC : Canon 5 133 13 GFC ∧ CFSG.KS.HNLocal.OM GFC = (CFSG.KS.HNLocal.OM LC)ᵀ :=
  tp_sound canon_LC tp_GFC

theorem land_mod21 (x : ℕ) : Nat.land x 2097151 = x % 2 ^ 21 := by
  rw [show (2097151 : ℕ) = 2 ^ 21 - 1 by norm_num]
  exact Nat.and_two_pow_sub_one_eq_mod x 21

noncomputable abbrev cf (j : ℕ) : ℕ := TD j % 2 ^ 21

noncomputable abbrev cn (j : ℕ) : ℕ := TD j / 2 ^ 21 % 512

theorem cf_zero : cf 0 = 1 := by
  rw [cf, ← land_mod21]
  exact Nat.eq_of_beq_eq_true td0

theorem cf_last : cf 8572 = 1140000 := by
  rw [cf, ← land_mod21]
  exact Nat.eq_of_beq_eq_true tdn

theorem cf_succ (j : ℕ) (hj : j < 8572) : cf j + cn j = cf (j + 1) :=
  (CFSG.KS.HNLocal.treeLeaf_sound consts masks msf cm cGA.1 cGB.1 cGFC.1 (leaf_lt j hj)).1

theorem find_leaf {k : ℕ} (hk1 : 1 ≤ k) (hk : k < 1140000) :
    ∃ j < 8572, cf j ≤ k ∧ k < cf j + cn j := by
  have key : ∀ J ≤ 8572, k < cf J → ∃ j < J, cf j ≤ k ∧ k < cf j + cn j := by
    intro J
    induction J with
    | zero => intro _ h; rw [cf_zero] at h; omega
    | succ J ih =>
      intro hJ h
      by_cases hkJ : k < cf J
      · obtain ⟨j, hj, h'⟩ := ih (by omega) hkJ
        exact ⟨j, by omega, h'⟩
      · refine ⟨J, by omega, by omega, ?_⟩
        rw [cf_succ J (by omega)]
        exact h
  exact key 8572 le_rfl (by rw [cf_last]; exact hk)

theorem sortLeaf_of {N lo n lo' n' : ℕ} (h : sortRange XC SD N M lo n = true) (hN : N = 1140000)
    (hlo : lo = lo') (hn : n = n') {m : ℕ} (h1 : lo' ≤ m) (h2 : m < lo' + n') :
    sortLeaf XC SD 1140000 M m = true := by
  subst hN hlo hn
  have := CFSG.KS.HNLocal.sortRange_spec h (m - lo) (by omega)
  rwa [Nat.add_sub_cancel' h1] at this

theorem sortLeaf_all {m : ℕ} (hm : m < 8572) : sortLeaf XC SD 1140000 M m = true := by
  rcases Nat.lt_or_ge m 2143 with h | h
  · exact sortLeaf_of so0 (by decide) (by decide) (lo' := 0) (n' := 2143) (by decide)
      (Nat.zero_le m) (by omega)
  rcases Nat.lt_or_ge m 4286 with h' | h'
  · exact sortLeaf_of so1 (by decide) (lo' := 2143) (n' := 2143) (by decide) (by decide) h
      (by omega)
  rcases Nat.lt_or_ge m 6429 with h'' | h''
  · exact sortLeaf_of so2 (by decide) (lo' := 4286) (n' := 2143) (by decide) (by decide) h'
      (by omega)
  · exact sortLeaf_of so3 (by decide) (lo' := 6429) (n' := 2143) (by decide) (by decide) h''
      (by omega)

theorem sig_zero_lt : 0 < 1140000 → sig SD 0 < 1140000 := by
  intro _
  have := (CFSG.KS.HNLocal.sortLeaf_spec (sortLeaf_all (m := 0) (by norm_num))).1 (by norm_num)
  simpa using this

theorem sig_step : ∀ i, i + 1 < 1140000 → sig SD (i + 1) < 1140000 ∧
    recX XC M (sig SD i) < recX XC M (sig SD (i + 1)) := by
  intro i hi
  have h := (CFSG.KS.HNLocal.sortLeaf_spec (sortLeaf_all (m := i / 133) (by omega))).2 (i % 133)
    (Nat.mod_lt _ (by norm_num)) (by omega)
  rw [show 133 * (i / 133) + i % 133 = i by omega] at h
  exact h

theorem key_min_of_order {n : Nat} {key σ : Nat → Nat} (h0 : 0 < n → σ 0 < n)
    (h : ∀ i, i + 1 < n → σ (i + 1) < n ∧ key (σ i) < key (σ (i + 1))) :
    ∀ k < n, key (σ 0) ≤ key k := by
  have hlt : ∀ i < n, σ i < n := by
    intro i hi
    rcases i with _ | i
    · exact h0 (by omega)
    · exact (h i hi).1
  have hmono : ∀ i j, i < j → j < n → key (σ i) < key (σ j) := by
    intro i j hij hj
    induction j with
    | zero => omega
    | succ j ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h' | rfl
      · exact lt_trans (ih h' (by omega)) (h j hj).2
      · exact (h i hj).2
  have hinj : ∀ i < n, ∀ j < n, σ i = σ j → i = j := by
    intro i hi j hj e
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h' | h'
    · have := hmono i j h' hj; rw [e] at this; exact lt_irrefl _ this
    · have := hmono j i h' hi; rw [e] at this; exact lt_irrefl _ this
  let f : Fin n → Fin n := fun i => ⟨σ i, hlt i i.2⟩
  have hf : Function.Injective f := fun i j e => Fin.ext (hinj i i.2 j j.2 (congrArg Fin.val e))
  intro k hk
  obtain ⟨i, hi⟩ := (Finite.injective_iff_surjective.1 hf) ⟨k, hk⟩
  have ei : σ i = k := congrArg Fin.val hi
  rw [← ei]
  rcases Nat.eq_zero_or_pos i.val with h' | h'
  · have e0 : i = ⟨0, by omega⟩ := Fin.ext h'
    rw [e0]
  · exact (hmono 0 i h' i.2).le

theorem sig_zero_pos : 0 < recX XC M (sig SD 0) :=
  Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_of_ble_eq_true (by quickRfl))

theorem recX_pos : ∀ k < 1140000, 0 < recX XC M k := fun k hk =>
  Nat.lt_of_lt_of_le sig_zero_pos (key_min_of_order sig_zero_lt sig_step k hk)

theorem XC_lt : ∀ i < 8572, XC i < 2 ^ 53200 := by
  have h : CFSG.KC.Loop.allBelow 8572 135 (fun i => Nat.beq (Nat.shiftRight (XC i) 53200) 0) =
      true := by quickRfl
  intro i hi
  have := Nat.eq_of_beq_eq_true (CFSG.KS.HNLocal.allBelow_spec h i hi (by omega))
  rw [show (XC i).shiftRight 53200 = XC i / 2 ^ 53200 from Nat.shiftRight_eq_div_pow _ _] at this
  rcases Nat.div_eq_zero_iff.1 this with h' | h'
  · exact absurd h' (Nat.two_pow_pos _).ne'
  · exact h'

theorem cf_le : ∀ j ≤ 8572, cf j ≤ 1140000 := by
  have key : ∀ d j, j + d = 8572 → cf j ≤ 1140000 := by
    intro d
    induction d with
    | zero => intro j hj; rw [show j = 8572 by omega, cf_last]
    | succ d ih =>
      intro j hj
      have h1 := cf_succ j (by omega)
      have h2 := ih (j + 1) (by omega)
      omega
  intro j hj
  exact key (8572 - j) j (by omega)

theorem mat_a_T : mat Dt (a Dt) = (CFSG.KS.HNLocal.OM GA)ᵀ := by
  rw [cGA.2, Matrix.transpose_transpose, mat_a]
  rfl

theorem mat_b_T : mat Dt (b Dt) = (CFSG.KS.HNLocal.OM GB)ᵀ := by
  rw [cGB.2, Matrix.transpose_transpose, mat_b]
  rfl

theorem child_of {k : ℕ} (hk1 : 1 ≤ k) (hk : k < 1140000) : ∃ p < k,
    CFSG.KS.HNLocal.CCanon (recX XC M k) ∧ (Xk k = a Dt • Xk p ∨ Xk k = b Dt • Xk p) := by
  obtain ⟨j, hj, h1, h2⟩ := find_leaf hk1 hk
  obtain ⟨-, hch, -⟩ :=
    CFSG.KS.HNLocal.treeLeaf_sound consts masks msf cm cGA.1 cGB.1 cGFC.1 (leaf_lt j hj)
  have hcf : cf j = TD j % 2 ^ 21 := rfl
  have hcn : cn j = TD j / 2 ^ 21 % 512 := rfl
  have hX : ∀ i < TD (j + 1) % 2 ^ 21 / 133, XC i < 2 ^ 53200 := fun i hi =>
    XC_lt i (by have : cf (j + 1) ≤ 1140000 := cf_le (j + 1) (by omega); simp only [cf] at this; omega)
  have hpos : ∀ t < TD j / 2 ^ 21 % 512, 0 < recX XC M (TD j % 2 ^ 21 + t) := fun t ht =>
    recX_pos _ (by
      have h1 : cf (j + 1) ≤ 1140000 := cf_le (j + 1) (by omega)
      have h2 : cf j + cn j = cf (j + 1) := cf_succ j hj
      simp only [cf, cn] at h1 h2
      omega)
  obtain ⟨r, -, hpk, hcan, hv⟩ := hch hX hpos (k - cf j) (by omega)
  have e : TD j % 2 ^ 21 + (k - cf j) = k := by omega
  rw [e] at hpk hcan hv
  refine ⟨133 * j + r, hpk, hcan, ?_⟩
  rcases hv with hv | hv
  · left
    rw [smul_vec, mat_a_T]
    exact hv
  · right
    rw [smul_vec, mat_b_T]
    exact hv

theorem Xk_zero : Xk 0 = rootV := by
  unfold Xk rootV
  rw [Nat.eq_of_beq_eq_true x0]

theorem orbit_step {x y : Vec Dt} (hy : y ∈ MulAction.orbit (J Dt) rootV)
    (h : x = a Dt • y ∨ x = b Dt • y) : x ∈ MulAction.orbit (J Dt) rootV := by
  rcases h with rfl | rfl
  · exact MulAction.mem_orbit_of_mem_orbit _ hy
  · exact MulAction.mem_orbit_of_mem_orbit _ hy

theorem Xk_mem_orbit : ∀ k < 1140000, Xk k ∈ MulAction.orbit (J Dt) rootV := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    by_cases hk0 : k = 0
    · rw [hk0, Xk_zero]
      exact MulAction.mem_orbit_self _
    · obtain ⟨p, hp, -, h⟩ := child_of (k := k) (Nat.pos_of_ne_zero hk0) hk
      exact orbit_step (ih p hp (lt_trans hp hk)) h

theorem Xk_canon {k : ℕ} (hk : k < 1140000) : CFSG.KS.HNLocal.CCanon (recX XC M k) := by
  rcases k with _ | k
  · rw [Nat.eq_of_beq_eq_true x0]
    exact root_canon
  · obtain ⟨-, -, h, -⟩ := child_of (k := k + 1) (by omega) hk
    exact h

theorem recX_injOn : ∀ i < 1140000, ∀ j < 1140000, recX XC M i = recX XC M j → i = j :=
  injOn_of_order (σ := sig SD) sig_zero_lt sig_step

theorem Xk_injective : ∀ i < 1140000, ∀ j < 1140000, Xk i = Xk j → i = j := fun i hi j hj e =>
  recX_injOn i hi j hj (CFSG.KS.HNLocal.cvec_inj (Xk_canon hi) (Xk_canon hj) e)

theorem card_orbit_ge : 1140000 ≤ Nat.card (MulAction.orbit (J Dt) rootV) := by
  have hf : Function.Injective fun k : Fin 1140000 =>
      (⟨Xk k.val, Xk_mem_orbit k.val k.2⟩ : MulAction.orbit (J Dt) rootV) :=
    fun i j e => Fin.ext (Xk_injective i.val i.2 j.val j.2 (congrArg Subtype.val e))
  have := Nat.card_le_card_of_injective _ hf
  simpa using this

abbrev P2 (k : ℕ) : Prop := ∀ i : Fin 133, i.val < 56 →
  ((CFSG.KS.HNLocal.OM GFC)ᵀ *ᵥ CFSG.KS.HNLocal.cvec (recX XC M k)) i = 0

abbrev P4 (k : ℕ) : Prop := ∀ i : Fin 133, 56 ≤ i.val → i.val < 120 →
  ((CFSG.KS.HNLocal.OM GFC)ᵀ *ᵥ CFSG.KS.HNLocal.cvec (recX XC M k)) i = 0

theorem card_blocks (P : ℕ → Prop) [DecidablePred P] :
    ((Finset.range 1140000).filter P).card = ∑ j ∈ Finset.range 8572,
      ((Finset.range (min (1140000 - 133 * j) 133)).filter fun r => P (133 * j + r)).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun k => k / 133) (t := Finset.range 8572) ?_]
  · refine Finset.sum_congr rfl fun j hj => ?_
    have hj' := Finset.mem_range.1 hj
    refine Finset.card_nbij' (fun k => k - 133 * j) (fun r => 133 * j + r) ?_ ?_ ?_ ?_
    · intro k hk
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hk ⊢
      obtain ⟨⟨h1, h2⟩, h3⟩ := hk
      have e : 133 * j + (k - 133 * j) = k := by omega
      refine ⟨by omega, ?_⟩
      rw [e]
      exact h2
    · intro r hr
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hr ⊢
      obtain ⟨h1, h2⟩ := hr
      exact ⟨⟨by omega, h2⟩, by omega⟩
    · intro k hk
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hk
      dsimp only
      omega
    · intro r hr
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hr
      dsimp only
      omega
  · intro k hk
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hk ⊢
    omega

theorem leaf_split (j : ℕ) (hj : j < 8572) :
    TL j = ((Finset.range (min (1140000 - 133 * j) 133)).filter fun r => P2 (133 * j + r)).card +
      2 ^ 24 * ((Finset.range (min (1140000 - 133 * j) 133)).filter fun r => P4 (133 * j + r)).card :=
  (CFSG.KS.HNLocal.treeLeaf_sound consts masks msf cm cGA.1 cGB.1 cGFC.1 (leaf_lt j hj)).2.2

theorem fix_counts : ((Finset.range 1140000).filter P2).card = 8800 ∧
    ((Finset.range 1140000).filter P4).card = 800 := by
  have h := leaves_sum
  have hs : ∑ j ∈ Finset.range 8572, TL j = ∑ j ∈ Finset.range 8572,
      (((Finset.range (min (1140000 - 133 * j) 133)).filter fun r => P2 (133 * j + r)).card +
        2 ^ 24 * ((Finset.range (min (1140000 - 133 * j) 133)).filter
          fun r => P4 (133 * j + r)).card) :=
    Finset.sum_congr rfl fun j hj => leaf_split j (Finset.mem_range.1 hj)
  have key : ∀ A B : ℕ → ℕ,
      ∑ j ∈ Finset.range 8572, (A j + 2 ^ 24 * B j) = 8800 + 2 ^ 24 * 800 →
      (∀ j ∈ Finset.range 8572, A j ≤ 133) →
      ∑ j ∈ Finset.range 8572, A j = 8800 ∧ ∑ j ∈ Finset.range 8572, B j = 800 := by
    intro A B hAB hA
    rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hAB
    have hle : ∑ j ∈ Finset.range 8572, A j ≤ ∑ _j ∈ Finset.range 8572, 133 :=
      Finset.sum_le_sum hA
    rw [Finset.sum_const, Finset.card_range, smul_eq_mul] at hle
    constructor <;> omega
  rw [card_blocks P2, card_blocks P4]
  refine key (fun j => ((Finset.range (min (1140000 - 133 * j) 133)).filter
      fun r => P2 (133 * j + r)).card) (fun j => ((Finset.range (min (1140000 - 133 * j) 133)).filter
      fun r => P4 (133 * j + r)).card) (hs.symm.trans h) fun j _ => ?_
  refine le_trans (Finset.card_filter_le _ _) ?_
  rw [Finset.card_range]
  exact Nat.min_le_right _ _

noncomputable abbrev T2F : Nat :=
  redP 13 CFSG.KD.OrdHN.L CFSG.KD.OrdHN.H 5 9 (Nat.add (RB 13) (Nat.mul 4 CFSG.KD.OrdHN.ONE))

noncomputable abbrev T4F : Nat :=
  redP 13 CFSG.KD.OrdHN.L CFSG.KD.OrdHN.H 5 9 (Nat.add (RB 14) (Nat.mul 4 CFSG.KD.OrdHN.ONE))

noncomputable abbrev LC2 : Nat := Nat.land LC (Nat.sub (Nat.shiftLeft 1 96824) 1)

noncomputable abbrev LC4 : Nat := Nat.land (Nat.shiftRight LC 96824) (Nat.sub (Nat.shiftLeft 1 110656) 1)

theorem pf2' : mul PF2 T2F = LC2 := Nat.eq_of_beq_eq_true pf2
theorem qf2' : mul QF2 LC2 = T2F := Nat.eq_of_beq_eq_true qf2
theorem pf4' : mul PF4 T4F = LC4 := Nat.eq_of_beq_eq_true pf4
theorem qf4' : mul QF4 LC4 = T4F := Nat.eq_of_beq_eq_true qf4

theorem LC2_eq : LC2 = Nat.land (Nat.shiftRight LC (1729 * 0)) (2 ^ (1729 * 56) - 1) := by
  have h2 : Nat.shiftRight LC (1729 * 0) = LC := Nat.shiftRight_zero
  have h3 : (1729 * 56 : ℕ) = 96824 := by norm_num
  rw [h2, h3]
  change Nat.land LC ((1 : ℕ) <<< 96824 - 1) = _
  rw [Nat.shiftLeft_eq, one_mul]

theorem LC4_eq : LC4 = Nat.land (Nat.shiftRight LC (1729 * 56)) (2 ^ (1729 * 64) - 1) := by
  have h3 : (1729 * 56 : ℕ) = 96824 := by norm_num
  have h4 : (1729 * 64 : ℕ) = 110656 := by norm_num
  rw [h3, h4]
  change Nat.land (Nat.shiftRight LC 96824) ((1 : ℕ) <<< 110656 - 1) = _
  rw [Nat.shiftLeft_eq, one_mul]

theorem T_facts {r : Nat} (hr0 : 0 < r) (hr : r < 48) :
    Canon 5 133 13 (redP 13 CFSG.KD.OrdHN.L CFSG.KD.OrdHN.H 5 9 (Nat.add (RB r) (Nat.mul 4 CFSG.KD.OrdHN.ONE))) ∧
      CFSG.KS.HNLocal.OM (redP 13 CFSG.KD.OrdHN.L CFSG.KD.OrdHN.H 5 9
        (Nat.add (RB r) (Nat.mul 4 CFSG.KD.OrdHN.ONE))) = CFSG.KS.HNLocal.OM (RB r) - 1 :=
  CFSG.KS.HNLocal.subOne_sound consts (canon_root hr0 hr)

theorem mulVec_zero_iff {L T P Q : Matrix (Fin 133) (Fin 133) (ZMod 5)} (h1 : L = P * T) (h2 : T = Q * L)
    (x : Fin 133 → ZMod 5) : L *ᵥ x = 0 ↔ T *ᵥ x = 0 := by
  constructor
  · intro h
    rw [h2, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_zero]
  · intro h
    rw [h1, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_zero]

theorem fixed_iff_gen {A : Matrix (Fin 133) (Fin 133) (ZMod 5)} (x : Fin 133 → ZMod 5) :
    A *ᵥ x = x ↔ (A - 1) *ᵥ x = 0 := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero]

theorem fixed_iff {j r : Nat} (hj : j < 15) (hr : r = j + 1) (x : Vec Dt) :
    wG j • x = x ↔ (CFSG.KS.HNLocal.OM (RB r) - 1) *ᵥ x = 0 := by
  subst hr
  rw [smul_vec, mat_wG j hj]
  exact fixed_iff_gen x

theorem rows_mulVec {A B : Matrix (Fin 133) (Fin 133) (ZMod 5)} {m n : ℕ}
    (h : ∀ i j : Fin 133, B i j =
      if hc : i.val < n ∧ m + i.val < 133 then A ⟨m + i.val, hc.2⟩ j else 0)
    (x : Fin 133 → ZMod 5) :
    B *ᵥ x = 0 ↔ ∀ i : Fin 133, m ≤ i.val → i.val < m + n → (A *ᵥ x) i = 0 := by
  have hB : ∀ i : Fin 133, (B *ᵥ x) i =
      if hc : i.val < n ∧ m + i.val < 133 then (A *ᵥ x) ⟨m + i.val, hc.2⟩ else 0 := by
    intro i
    by_cases hc : i.val < n ∧ m + i.val < 133
    · rw [dif_pos hc]
      simp only [Matrix.mulVec, dotProduct, h, dif_pos hc]
    · rw [dif_neg hc]
      simp only [Matrix.mulVec, dotProduct, h, dif_neg hc, zero_mul, Finset.sum_const_zero]
  constructor
  · intro h0 i h1 h2
    have hc : i.val - m < n ∧ m + (i.val - m) < 133 := ⟨by omega, by omega⟩
    have key := hB ⟨i.val - m, by omega⟩
    rw [h0] at key
    dsimp only at key
    rw [dif_pos hc] at key
    have e : (⟨m + (i.val - m), hc.2⟩ : Fin 133) = i := Fin.ext (Nat.add_sub_cancel' h1)
    rw [e] at key
    exact key.symm
  · intro h0
    funext i
    rw [hB]
    split_ifs with hc
    · exact h0 _ (Nat.le_add_right _ _) (Nat.add_lt_add_left hc.1 m)
    · rfl

theorem P2_iff (k : Nat) : P2 k ↔ wG 12 • Xk k = Xk k := by
  have hT := T_facts (r := 13) (by norm_num) (by norm_num)
  have e1 : mulR 5 13 1729 133 9 CFSG.KD.OrdHN.L CFSG.KD.OrdHN.H CFSG.KD.OrdHN.CM CFSG.KD.OrdHN.RM
      PF2 (redP 13 CFSG.KD.OrdHN.L CFSG.KD.OrdHN.H 5 9
        (Nat.add (RB 13) (Nat.mul 4 CFSG.KD.OrdHN.ONE))) = LC2 := pf2'
  have hP := mulR_sound consts (canon_of_valid v_PF2) hT.1
  rw [e1] at hP
  have e2 : mulR 5 13 1729 133 9 CFSG.KD.OrdHN.L CFSG.KD.OrdHN.H CFSG.KD.OrdHN.CM CFSG.KD.OrdHN.RM
      QF2 LC2 = redP 13 CFSG.KD.OrdHN.L CFSG.KD.OrdHN.H 5 9
        (Nat.add (RB 13) (Nat.mul 4 CFSG.KD.OrdHN.ONE)) := qf2'
  have hQ := mulR_sound consts (canon_of_valid v_QF2) hP.1
  rw [e2] at hQ
  have hrows := (CFSG.KS.HNLocal.rows_sound (m := 0) (n := 56) canon_LC).2
  rw [← LC2_eq] at hrows
  have hf : wG 12 • Xk k = Xk k ↔ CFSG.KS.HNLocal.OM (redP 13 CFSG.KD.OrdHN.L CFSG.KD.OrdHN.H 5 9
      (Nat.add (RB 13) (Nat.mul 4 CFSG.KD.OrdHN.ONE))) *ᵥ Xk k = 0 := by
    rw [hT.2]
    exact fixed_iff (j := 12) (r := 13) (by norm_num) rfl (Xk k)
  refine Iff.trans ?_ hf.symm
  refine Iff.trans ?_ (mulVec_zero_iff hP.2 hQ.2 (Xk k))
  refine Iff.trans ?_ (rows_mulVec hrows (Xk k)).symm
  have hG : (CFSG.KS.HNLocal.OM GFC)ᵀ = CFSG.KS.HNLocal.OM LC := by
    rw [cGFC.2, Matrix.transpose_transpose]
  constructor
  · intro h i _ hi
    have := h i (by omega)
    rw [hG] at this
    exact this
  · intro h i hi
    rw [hG]
    exact h i (Nat.zero_le _) (by omega)

theorem P4_iff (k : Nat) : P4 k ↔ wG 13 • Xk k = Xk k := by
  have hT := T_facts (r := 14) (by norm_num) (by norm_num)
  have e1 : mulR 5 13 1729 133 9 CFSG.KD.OrdHN.L CFSG.KD.OrdHN.H CFSG.KD.OrdHN.CM CFSG.KD.OrdHN.RM
      PF4 (redP 13 CFSG.KD.OrdHN.L CFSG.KD.OrdHN.H 5 9
        (Nat.add (RB 14) (Nat.mul 4 CFSG.KD.OrdHN.ONE))) = LC4 := pf4'
  have hP := mulR_sound consts (canon_of_valid v_PF4) hT.1
  rw [e1] at hP
  have e2 : mulR 5 13 1729 133 9 CFSG.KD.OrdHN.L CFSG.KD.OrdHN.H CFSG.KD.OrdHN.CM CFSG.KD.OrdHN.RM
      QF4 LC4 = redP 13 CFSG.KD.OrdHN.L CFSG.KD.OrdHN.H 5 9
        (Nat.add (RB 14) (Nat.mul 4 CFSG.KD.OrdHN.ONE)) := qf4'
  have hQ := mulR_sound consts (canon_of_valid v_QF4) hP.1
  rw [e2] at hQ
  have hrows := (CFSG.KS.HNLocal.rows_sound (m := 56) (n := 64) canon_LC).2
  rw [← LC4_eq] at hrows
  have hf : wG 13 • Xk k = Xk k ↔ CFSG.KS.HNLocal.OM (redP 13 CFSG.KD.OrdHN.L CFSG.KD.OrdHN.H 5 9
      (Nat.add (RB 14) (Nat.mul 4 CFSG.KD.OrdHN.ONE))) *ᵥ Xk k = 0 := by
    rw [hT.2]
    exact fixed_iff (j := 13) (r := 14) (by norm_num) rfl (Xk k)
  refine Iff.trans ?_ hf.symm
  refine Iff.trans ?_ (mulVec_zero_iff hP.2 hQ.2 (Xk k))
  refine Iff.trans ?_ (rows_mulVec hrows (Xk k)).symm
  have hG : (CFSG.KS.HNLocal.OM GFC)ᵀ = CFSG.KS.HNLocal.OM LC := by
    rw [cGFC.2, Matrix.transpose_transpose]
  constructor
  · intro h i h1 h2
    have := h i h1 (by omega)
    rw [hG] at this
    exact this
  · intro h i h1 h2
    rw [hG]
    exact h i h1 (by omega)

theorem card_fin_subtype {N : ℕ} (Q : ℕ → Prop) [DecidablePred Q] :
    Nat.card {k : Fin N // Q k.val} = ((Finset.range N).filter Q).card := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter, Finset.card_filter]
  exact Fin.sum_univ_eq_sum_range (fun k => if Q k then 1 else 0) N

theorem card_fix_t2 : Nat.card {k : Fin 1140000 // wG 12 • Xk k.val = Xk k.val} = 8800 := by
  classical
  rw [card_fin_subtype (fun k => wG 12 • Xk k = Xk k)]
  have e : (Finset.range 1140000).filter (fun k => wG 12 • Xk k = Xk k) =
      (Finset.range 1140000).filter P2 := Finset.filter_congr fun k _ => (P2_iff k).symm
  rw [e]
  exact fix_counts.1

theorem card_fix_t4 : Nat.card {k : Fin 1140000 // wG 13 • Xk k.val = Xk k.val} = 800 := by
  classical
  rw [card_fin_subtype (fun k => wG 13 • Xk k = Xk k)]
  have e : (Finset.range 1140000).filter (fun k => wG 13 • Xk k = Xk k) =
      (Finset.range 1140000).filter P4 := Finset.filter_congr fun k _ => (P4_iff k).symm
  rw [e]
  exact fix_counts.2

end CertificateChecks.KernelHNLocal

end
