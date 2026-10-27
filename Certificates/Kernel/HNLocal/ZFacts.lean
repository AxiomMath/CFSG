module

public import Certificates.Kernel.HNLocal.ZRegs
public import CFSG.Certificates.Kernel.HNLocal.ZCen
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporZTwo
import Certificates.Kernel.HNLocal.Checks.ZR
import Certificates.Kernel.HNLocal.Checks.Z0
import Certificates.Kernel.HNLocal.Checks.Z1
import Certificates.Kernel.HNLocal.Checks.Z2
import Certificates.Kernel.HNLocal.Checks.Z3
import Certificates.Kernel.HN3166.Seed
import CFSG.Certificates.Kernel.Orders.HN.Checks.K
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Group

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelHNLocalZ

open CFSG.KC.Ord CFSG.KS.Ord CFSG.KD.HNLocalZ CFSG.Sporadic.F5 CFSG.Sporadic.HN.LocalK
open CFSG.Sporadic.Fi23 CFSG.Sporadic.Th CertificateChecks.KernelHNLocal
open CFSG.LocalAnalysis.WeakClosure81.SporHN CFSG.LocalAnalysis.WeakClosure81
open scoped commutatorElement

local notation "Dt" => CFSG.Sporadic.HN.Native.hnData

local notation "OM" => ordMat 5 (CFSG.Sporadic.F5.Native.F5Data.d CFSG.Sporadic.HN.Native.hnData) 13 1729

attribute [local irreducible] nfJ pcJ

theorem ev_vals : CFSG.KC.HNLocal.evAt EV 0 = 0 ∧ CFSG.KC.HNLocal.evAt EV 1 = 2560 ∧
    CFSG.KC.HNLocal.evAt EV 2 = 1536 ∧ EZ = 2560 := by
  decide +kernel

theorem ev_sep : ∀ s < 4, ∀ t < 4, s ≠ t →
    ∃ i < 14, CFSG.KS.HNLocal.bitsE (CFSG.KC.HNLocal.evAt EV s) i ≠
      CFSG.KS.HNLocal.bitsE (CFSG.KC.HNLocal.evAt EV t) i := by
  decide +kernel

theorem bitsE_lt (x i : ℕ) : CFSG.KS.HNLocal.bitsE x i < 2 := Nat.mod_lt _ (by norm_num)

theorem pcTie_eq : ∀ k < 14, RZ (64 + k) = CFSG.KD.HNLocal.PC k := by
  intro k hk
  interval_cases k
  · exact Nat.eq_of_beq_eq_true pcTie0
  · exact Nat.eq_of_beq_eq_true pcTie1
  · exact Nat.eq_of_beq_eq_true pcTie2
  · exact Nat.eq_of_beq_eq_true pcTie3
  · exact Nat.eq_of_beq_eq_true pcTie4
  · exact Nat.eq_of_beq_eq_true pcTie5
  · exact Nat.eq_of_beq_eq_true pcTie6
  · exact Nat.eq_of_beq_eq_true pcTie7
  · exact Nat.eq_of_beq_eq_true pcTie8
  · exact Nat.eq_of_beq_eq_true pcTie9
  · exact Nat.eq_of_beq_eq_true pcTie10
  · exact Nat.eq_of_beq_eq_true pcTie11
  · exact Nat.eq_of_beq_eq_true pcTie12
  · exact Nat.eq_of_beq_eq_true pcTie13

theorem mat_pcJ' {k : ℕ} (hk : k < 14) : mat Dt (pcJ k) = Mr (63 + k) := by
  have e : 63 + k + 1 = 64 + k := by omega
  rw [mat_pcJ hk, Mr, e, pcTie_eq k hk]

@[expose] noncomputable def F (s : ℕ) : J Dt :=
  nfJ (CFSG.KS.HNLocal.bitsE (CFSG.KC.HNLocal.evAt EV s))

@[expose] noncomputable def zJ : J Dt := F 1

@[expose] noncomputable def w0J : J Dt := F 2

theorem F_mem (s : ℕ) : F s ∈ QJ := nfJ_mem _

theorem F_zero : F 0 = 1 := by
  unfold F
  rw [ev_vals.1]
  unfold nfJ
  simp [CFSG.KS.HNLocal.bitsE]

theorem F_ne {s t : ℕ} (hs : s < 4) (ht : t < 4) (hst : s ≠ t) : F s ≠ F t := fun h => by
  obtain ⟨i, hi, hne⟩ := ev_sep s hs t ht hst
  exact hne (nf_inj (bitsE_lt _) (bitsE_lt _) h i hi)

theorem zJ_eq : zJ = pcJ 9 * pcJ 11 := by
  unfold zJ F
  rw [ev_vals.2.1]
  unfold nfJ
  simp [CFSG.KS.HNLocal.bitsE, List.range'_succ]

theorem w0J_eq : w0J = pcJ 9 * pcJ 10 := by
  unfold w0J F
  rw [ev_vals.2.2.1]
  unfold nfJ
  simp [CFSG.KS.HNLocal.bitsE, List.range'_succ]

theorem zJ_ne_one : zJ ≠ 1 := by
  rw [← F_zero]
  exact F_ne (by norm_num) (by norm_num) (by norm_num)

theorem w0J_ne_one : w0J ≠ 1 := by
  rw [← F_zero]
  exact F_ne (by norm_num) (by norm_num) (by norm_num)

theorem w0J_ne_zJ : w0J ≠ zJ := F_ne (by norm_num) (by norm_num) (by norm_num)

@[expose] noncomputable def E0 (g : ℕ) : J Dt :=
  if g < 63 then wG g else if g < 77 then pcJ (g - 63) else if g = 77 then zJ else w0J

theorem lm_odd (g : ℕ) : lm (2 * g + 1) = Mr g := by
  rw [lm_eq, if_pos (by omega)]
  congr 1
  omega

theorem lm_even (g : ℕ) : lm (2 * g) = Mi g := by
  rw [lm_eq, if_neg (by omega)]
  congr 1
  omega

theorem mat_E0 {g : ℕ} (hg : g < 79) : mat Dt (E0 g) = Mr g := by
  unfold E0
  by_cases h1 : g < 63
  · rw [if_pos h1]
    exact mat_wG g h1
  rw [if_neg h1]
  by_cases h2 : g < 77
  · rw [if_pos h2, mat_pcJ' (by omega)]
    congr 1
    omega
  rw [if_neg h2]
  have hw : ∀ {k : ℕ} {a b g' : ℕ}, k < 127 → g' < 86 → WZL k = [2 * a + 1, 2 * b + 1] ++ [2 * g'] →
      a < 77 → 63 ≤ a → b < 77 → 63 ≤ b →
      mat Dt (pcJ (a - 63) * pcJ (b - 63)) = Mr g' := fun hk hg' hs ha1 ha2 hb1 hb2 => by
    rw [← word_root hk hg' hs, CertificateChecks.KernelHN.mat_mul', mat_pcJ' (by omega),
      mat_pcJ' (by omega)]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, lm_odd]
    congr 2 <;> omega
  by_cases h3 : g = 77
  · subst h3
    rw [if_pos rfl, zJ_eq]
    exact hw (k := 61) (a := 72) (b := 74) (by norm_num) (by norm_num) (by decide +kernel)
      (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · have h4 : g = 78 := by omega
    subst h4
    rw [if_neg (by norm_num), w0J_eq]
    exact hw (k := 62) (a := 72) (b := 73) (by norm_num) (by norm_num) (by decide +kernel)
      (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)

theorem allRep {n : ℕ} (hn : n ≤ 86) (h : ∀ g < n, Rep g) {u : List ℕ} (hu : ∀ c ∈ u, c / 2 < n) :
    ∀ c ∈ u, c / 2 < 86 ∧ Rep (c / 2) := fun c hc => ⟨Nat.lt_of_lt_of_le (hu c hc) hn, h _ (hu c hc)⟩

theorem rep_succ {n : ℕ} (h : ∀ g < n, Rep g) (hn : Rep n) : ∀ g < n + 1, Rep g := fun g hg => by
  rcases Nat.lt_succ_iff_lt_or_eq.1 hg with hg | rfl
  · exact h g hg
  · exact hn

theorem rep84 : ∀ g < 84, Rep g := by
  have r79 : ∀ g < 79, Rep g := fun g hg => ⟨E0 g, mat_E0 hg⟩
  have r80 := rep_succ r79 (rep_last (k := 63) (u := [0, 1, 0, 2]) (by norm_num) (by norm_num)
    (by decide +kernel) (allRep (by norm_num) r79 (by decide)))
  have r81 := rep_succ r80 (rep_last (k := 64) (u := [155, 159, 27, 158]) (by norm_num)
    (by norm_num) (by decide +kernel) (allRep (by norm_num) r80 (by decide)))
  have r82 := rep_succ r81 (rep_first (k := 65) (g := 81)
    (u := [161, 161, 161, 161, 161, 161, 161, 161, 159]) (by norm_num) (by decide +kernel)
    (allRep (by norm_num) r81 (by decide)))
  have r83 := rep_succ r82 (rep_last (k := 66) (u := [53, 51, 33, 51]) (by norm_num) (by norm_num)
    (by decide +kernel) (allRep (by norm_num) r82 (by decide)))
  exact rep_succ r83 (rep_last (k := 67) (u := [165, 163]) (by norm_num) (by norm_num)
    (by decide +kernel) (allRep (by norm_num) r83 (by decide)))

@[expose] noncomputable def hZ : J Dt := (rep84 83 (by norm_num)).choose

theorem mat_hZ : mat Dt hZ = Mr 83 := (rep84 83 (by norm_num)).choose_spec

@[expose] noncomputable def progZ (z : ℤ) : J Dt :=
  if 0 < z then wG (z.natAbs - 1) else (wG (z.natAbs - 1))⁻¹

@[expose] noncomputable def gZ : J Dt := wordG progZ hnGWord

@[expose] noncomputable def topZ (z : ℤ) : J Dt :=
  if z.natAbs ≤ 63 then progZ z else if 0 < z then gZ else gZ⁻¹

@[expose] def pcode (z : ℤ) : ℕ :=
  2 * (if z.natAbs = 64 then 85 else z.natAbs - 1) + (if 0 < z then 1 else 0)

theorem mat_progZ {z : ℤ} (hz : z ≠ 0) (h63 : z.natAbs ≤ 63) : mat Dt (progZ z) = lm (pcode z) := by
  unfold progZ pcode
  rw [if_neg (by omega : ¬ z.natAbs = 64)]
  have hw := mat_wG (z.natAbs - 1) (by omega)
  by_cases hp : 0 < z
  · rw [if_pos hp, if_pos hp, lm_odd, hw]
  · rw [if_neg hp, if_neg hp, Nat.add_zero, lm_even, mat_inv_of (by omega) hw]

theorem gWord_ok : WZL 70 = hnGWord.map pcode ++ [2 * 85] ∧
    ∀ z ∈ hnGWord, z ≠ 0 ∧ z.natAbs ≤ 63 := by
  decide +kernel

theorem mat_wordG' {f : ℤ → J Dt} (w : List ℤ) :
    mat Dt (wordG f w) = (w.map fun z => mat Dt (f z)).prod := by
  unfold wordG
  rw [mat_prod, List.map_map]
  rfl

theorem mat_gZ : mat Dt gZ = Mr 85 := by
  rw [← word_root (k := 70) (by norm_num) (by norm_num) gWord_ok.1, gZ, mat_wordG', List.map_map]
  congr 1
  exact List.map_congr_left fun z hz =>
    mat_progZ (gWord_ok.2 z hz).1 (gWord_ok.2 z hz).2

@[expose] noncomputable def wT : J Dt := hZ * w0J * hZ⁻¹

@[expose] noncomputable def E (g : ℕ) : J Dt :=
  if g < 79 then E0 g else if g = 83 then hZ else if g = 84 then wT else gZ

@[expose] def good (g : ℕ) : Prop := g < 79 ∨ (83 ≤ g ∧ g < 86)

instance (g : ℕ) : Decidable (good g) := inferInstanceAs (Decidable (g < 79 ∨ (83 ≤ g ∧ g < 86)))

theorem mat_wT : mat Dt wT = Mr 84 := by
  rw [← word_root (k := 69) (u := [167, 157, 166]) (by norm_num) (by norm_num) (by decide +kernel)]
  have h1 : (167 : ℕ) = 2 * 83 + 1 := rfl
  have h2 : (157 : ℕ) = 2 * 78 + 1 := rfl
  have h3 : (166 : ℕ) = 2 * 83 := rfl
  have hw := mat_E0 (g := 78) (by norm_num)
  unfold E0 at hw
  rw [if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num)] at hw
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rw [h1, h2, h3, lm_odd, lm_odd, lm_even, wT, CertificateChecks.KernelHN.mat_mul',
    CertificateChecks.KernelHN.mat_mul', mat_hZ, hw, mat_inv_of (by norm_num) mat_hZ, mul_assoc]

theorem mat_E {g : ℕ} (hg : good g) : mat Dt (E g) = Mr g := by
  unfold E
  rcases hg with hg | ⟨h1, h2⟩
  · rw [if_pos hg]
    exact mat_E0 hg
  rw [if_neg (by omega)]
  by_cases h83 : g = 83
  · subst h83
    rw [if_pos rfl]
    exact mat_hZ
  rw [if_neg h83]
  by_cases h84 : g = 84
  · subst h84
    rw [if_pos rfl]
    exact mat_wT
  have h85 : g = 85 := by omega
  rw [if_neg h84, h85]
  exact mat_gZ

@[expose] noncomputable def elC (c : ℕ) : J Dt := if c % 2 = 1 then E (c / 2) else (E (c / 2))⁻¹

theorem elC_odd (g : ℕ) : elC (2 * g + 1) = E g := by
  unfold elC
  rw [if_pos (by omega)]
  congr 1
  omega

theorem elC_even (g : ℕ) : elC (2 * g) = (E g)⁻¹ := by
  unfold elC
  rw [if_neg (by omega)]
  congr 2
  omega

theorem mat_elC {c : ℕ} (hc : good (c / 2)) : mat Dt (elC c) = lm c := by
  have h86 : c / 2 < 86 := by rcases hc with h | h <;> omega
  unfold elC
  rw [lm_eq]
  split_ifs
  · exact mat_E hc
  · exact mat_inv_of h86 (mat_E hc)

theorem rel_E {k : ℕ} (hk : k < 127) {l : List ℕ} (hs : WZL k = l) (hl : ∀ c ∈ l, good (c / 2)) :
    (l.map elC).prod = 1 := by
  apply mat_injective Dt
  rw [mat_prod, List.map_map, CertificateChecks.KernelHN.mat_one', ← word_one hk, hs]
  congr 1
  exact List.map_congr_left fun c hc => mat_elC (hl c hc)

theorem E_wG {j : ℕ} (hj : j < 63) : E j = wG j := by
  unfold E E0
  rw [if_pos (by omega), if_pos hj]

theorem E_pc {k : ℕ} (hk : k < 14) : E (63 + k) = pcJ k := by
  unfold E E0
  rw [if_pos (by omega), if_neg (by omega), if_pos (by omega)]
  congr 1
  omega

theorem E_77 : E 77 = zJ := by
  unfold E E0
  rw [if_pos (by norm_num), if_neg (by norm_num), if_neg (by norm_num), if_pos rfl]

theorem E_78 : E 78 = w0J := by
  unfold E E0
  rw [if_pos (by norm_num), if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num)]

theorem E_83 : E 83 = hZ := by
  unfold E
  rw [if_neg (by norm_num), if_pos rfl]

theorem E_84 : E 84 = wT := by
  unfold E
  rw [if_neg (by norm_num), if_neg (by norm_num), if_pos rfl]

theorem E_85 : E 85 = gZ := by
  unfold E
  rw [if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num)]

theorem rel2 {k a b : ℕ} (hk : k < 127) (hs : WZL k = [a, b]) (ha : good (a / 2))
    (hb : good (b / 2)) : elC a * elC b = 1 := by
  have h := rel_E hk hs (by simp [ha, hb])
  simpa using h

theorem rel4 {k a b c d : ℕ} (hk : k < 127) (hs : WZL k = [a, b, c, d]) (ha : good (a / 2))
    (hb : good (b / 2)) (hc : good (c / 2)) (hd : good (d / 2)) :
    elC a * elC b * elC c * elC d = 1 := by
  have h := rel_E hk hs (by simp [ha, hb, hc, hd])
  simpa [mul_assoc] using h

theorem rel5 {k a b c d f : ℕ} (hk : k < 127) (hs : WZL k = [a, b, c, d, f]) (ha : good (a / 2))
    (hb : good (b / 2)) (hc : good (c / 2)) (hd : good (d / 2)) (hf : good (f / 2)) :
    elC a * elC b * elC c * elC d * elC f = 1 := by
  have h := rel_E hk hs (by simp [ha, hb, hc, hd, hf])
  simpa [mul_assoc] using h

theorem good_pc {k : ℕ} (hk : k < 14) :
    good ((2 * (63 + k) + 1) / 2) ∧ good (2 * (63 + k) / 2) := by
  unfold good
  omega

theorem hZ_conj : hZ * zJ * hZ⁻¹ = wG 13 := by
  have h := rel4 (k := 68) (a := 2 * 83 + 1) (b := 2 * 77 + 1) (c := 2 * 83) (d := 2 * 13)
    (by norm_num) (by decide +kernel) (by decide) (by decide) (by decide) (by decide)
  rw [elC_odd, elC_odd, elC_even, elC_even, E_83, E_77, E_wG (by norm_num), mul_inv_eq_one] at h
  exact h

theorem zJ_sq : zJ * zJ = 1 := by
  have h := rel2 (k := 98) (a := 2 * 77 + 1) (b := 2 * 77 + 1) (by norm_num) (by decide +kernel)
    (by decide) (by decide)
  rwa [elC_odd, E_77] at h

theorem z_shape : ∀ k < 14,
    WZL (99 + 2 * k) = [2 * 77 + 1, 2 * (63 + k) + 1, 2 * 77, 2 * (63 + k)] := by
  decide +kernel

theorem w_shape : ∀ k < 14,
    WZL (100 + 2 * k) = [2 * 78 + 1, 2 * (63 + k) + 1, 2 * 78, 2 * (63 + k)] ∨
      WZL (100 + 2 * k) = [2 * 78 + 1, 2 * (63 + k) + 1, 2 * 78, 2 * (63 + k), 2 * 77] := by
  decide +kernel

theorem w_shape1 : WZL 102 = [2 * 78 + 1, 2 * (63 + 1) + 1, 2 * 78, 2 * (63 + 1), 2 * 77] := by
  decide +kernel

theorem zJ_comm_pc {k : ℕ} (hk : k < 14) : zJ * pcJ k = pcJ k * zJ := by
  have h := rel4 (by omega) (z_shape k hk) (by decide) (good_pc hk).1 (by decide) (good_pc hk).2
  rw [elC_odd, elC_odd, elC_even, elC_even, E_77, E_pc hk, ← commutatorElement_def,
    commutatorElement_eq_one_iff_mul_comm] at h
  exact h

theorem w0J_comm_pc {k : ℕ} (hk : k < 14) : ⁅w0J, pcJ k⁆ = 1 ∨ ⁅w0J, pcJ k⁆ = zJ := by
  rcases w_shape k hk with hs | hs
  · have h := rel4 (by omega) hs (by decide) (good_pc hk).1 (by decide) (good_pc hk).2
    rw [elC_odd, elC_odd, elC_even, elC_even, E_78, E_pc hk, ← commutatorElement_def] at h
    exact Or.inl h
  · have h := rel5 (by omega) hs (by decide) (good_pc hk).1 (by decide) (good_pc hk).2 (by decide)
    rw [elC_odd, elC_odd, elC_even, elC_even, elC_even, E_78, E_pc hk, E_77,
      ← commutatorElement_def, mul_inv_eq_one] at h
    exact Or.inr h

theorem w0J_comm_pc1 : ⁅w0J, pcJ 1⁆ = zJ := by
  have h := rel5 (by norm_num) w_shape1 (by decide) (good_pc (k := 1) (by norm_num)).1 (by decide)
    (good_pc (k := 1) (by norm_num)).2 (by decide)
  rw [elC_odd, elC_odd, elC_even, elC_even, elC_even, E_78, E_pc (by norm_num), E_77,
    ← commutatorElement_def, mul_inv_eq_one] at h
  exact h

theorem gZ_conj_t : gZ * wG 13 * gZ⁻¹ = wT := by
  have h := rel4 (k := 71) (a := 2 * 85 + 1) (b := 2 * 13 + 1) (c := 2 * 85) (d := 2 * 84)
    (by norm_num) (by decide +kernel) (by decide) (by decide) (by decide) (by decide)
  rw [elC_odd, elC_odd, elC_even, elC_even, E_85, E_84, E_wG (by norm_num), mul_inv_eq_one] at h
  exact h

theorem gZ_conj_w : gZ * wT * gZ⁻¹ = wG 13 * wT := by
  have h := rel5 (k := 72) (a := 2 * 85 + 1) (b := 2 * 84 + 1) (c := 2 * 85) (d := 2 * 84)
    (f := 2 * 13) (by norm_num) (by decide +kernel) (by decide) (by decide) (by decide) (by decide)
    (by decide)
  rw [elC_odd, elC_odd, elC_even, elC_even, elC_even, E_85, E_84, E_wG (by norm_num),
    mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h
  exact h

@[expose] noncomputable def pcS : Set (J Dt) := {x | ∃ k < 14, x = pcJ k}

theorem QJ_le : ∀ y ∈ QJ, y ∈ Subgroup.closure pcS := fun y hy => by
  obtain ⟨e, -, rfl⟩ := nf_surj hy
  unfold nfJ
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
  rw [List.mem_range'] at hi
  have hi' : pcJ i ∈ pcS := ⟨i, by omega, rfl⟩
  exact pow_mem (Subgroup.subset_closure hi') _

theorem zJ_comm_pcS : ∀ s ∈ pcS, zJ * s = s * zJ := fun s hs => by
  obtain ⟨k, hk, rfl⟩ := hs
  exact zJ_comm_pc hk

theorem w0J_comm_pcS : ∀ s ∈ pcS, ⁅w0J, s⁆ = 1 ∨ ⁅w0J, s⁆ = zJ := fun s hs => by
  obtain ⟨k, hk, rfl⟩ := hs
  exact w0J_comm_pc hk

theorem zJ_central : ∀ p ∈ QJ, zJ * p = p * zJ := by
  intro p hp
  have hp' : p ∈ Subgroup.closure pcS := QJ_le p hp
  have hle : Subgroup.closure pcS ≤ Subgroup.centralizer {zJ} :=
    (Subgroup.closure_le _).2 fun s hs =>
      Subgroup.mem_centralizer_singleton_iff.2 (zJ_comm_pcS s hs).symm
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hp')).symm

@[expose] noncomputable def VQ : Subgroup (J Dt) := zTwoOf QJ zJ zJ_central zJ_sq

theorem zJ_mem_VQ : zJ ∈ VQ :=
  mem_zTwoOf.2 ⟨F_mem 1, fun p hp => Or.inl (commutatorElement_eq_one_iff_mul_comm.2
    (zJ_central p hp))⟩

theorem w0J_mem_VQ : w0J ∈ VQ :=
  mem_zTwoOf.2 ⟨F_mem 2, fun p hp => by
    have hz : ∀ q ∈ Subgroup.closure pcS, zJ * q = q * zJ := fun q hq => by
      have hle : Subgroup.closure pcS ≤ Subgroup.centralizer {zJ} :=
        (Subgroup.closure_le _).2 fun s hs =>
          Subgroup.mem_centralizer_singleton_iff.2 (zJ_comm_pcS s hs).symm
      exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hq)).symm
    exact commutatorElement_mem_pair_of_mem_closure (S := pcS) (x := w0J) (z := zJ) hz zJ_sq
      w0J_comm_pcS (QJ_le p hp)⟩

open CFSG.KD.HNLocalZ in
theorem zChunk_ok {m : ℕ} (hm : m < 16) : zChunk m = true := by
  interval_cases m
  · exact zChunk0
  · exact zChunk1
  · exact zChunk2
  · exact zChunk3
  · exact zChunk4
  · exact zChunk5
  · exact zChunk6
  · exact zChunk7
  · exact zChunk8
  · exact zChunk9
  · exact zChunk10
  · exact zChunk11
  · exact zChunk12
  · exact zChunk13
  · exact zChunk14
  · exact zChunk15

theorem zTwo_nf {y : J Dt} (hy : y ∈ QJ)
    (h : ∀ k < 14, ⁅y, pcJ k⁆ = 1 ∨ ⁅y, pcJ k⁆ = zJ) : ∃ s < 4, y = F s := by
  obtain ⟨e, he, rfl⟩ := nf_surj hy
  have h0 := he 0
  have h1 := he 1
  have h2 := he 2
  have h3 := he 3
  have hm : e 0 + 2 * e 1 + 4 * e 2 + 8 * e 3 < 16 := by omega
  rcases CFSG.KS.HNLocal.zcenAt_sound CFSG.KD.OrdHN.consts
      (fun i hi => canon_PC i (by omega)) (by norm_num) (by norm_num; omega) (zChunk_ok hm) e he
      (fun i hi => by interval_cases i <;> omega) with ⟨s, hs, hse⟩ | ⟨j, hj, hne1, hne2⟩
  · exact ⟨s, hs, nfJ_congr hse⟩
  · exfalso
    have hz : mat Dt zJ = CFSG.KS.HNLocal.nfE CFSG.KD.HNLocal.PC 14 (CFSG.KS.HNLocal.bitsE EZ) := by
      rw [zJ, F, mat_nfJ, ev_vals.2.1, ev_vals.2.2.2]
    rcases h j hj with hc | hc
    · rw [commutatorElement_eq_one_iff_mul_comm] at hc
      apply hne1
      have := congrArg (mat Dt) hc
      rwa [CertificateChecks.KernelHN.mat_mul', CertificateChecks.KernelHN.mat_mul', mat_nfJ,
        mat_pcJ hj] at this
    · rw [commutatorElement_def] at hc
      have hc' : nfJ e * pcJ j = zJ * pcJ j * nfJ e := by
        rw [← hc]
        group
      apply hne2
      have := congrArg (mat Dt) hc'
      rwa [CertificateChecks.KernelHN.mat_mul', CertificateChecks.KernelHN.mat_mul',
        CertificateChecks.KernelHN.mat_mul', mat_nfJ, mat_pcJ hj, hz] at this

theorem F_three : F 3 = zJ * w0J := by
  have hmem := mul_mem zJ_mem_VQ w0J_mem_VQ
  obtain ⟨hQ, hc⟩ := mem_zTwoOf.1 hmem
  obtain ⟨s, hs, hse⟩ := zTwo_nf hQ fun k hk => hc _ (pcJ_mem k)
  have hzinv : zJ⁻¹ = zJ := inv_eq_of_mul_eq_one_right zJ_sq
  interval_cases s
  · exfalso
    rw [F_zero] at hse
    exact w0J_ne_zJ ((eq_inv_of_mul_eq_one_right hse).trans hzinv)
  · exfalso
    exact w0J_ne_one (mul_eq_left.1 hse)
  · exfalso
    exact zJ_ne_one (mul_eq_right.1 hse)
  · exact hse.symm

theorem mem_zTwo_QJ {y : J Dt} :
    (y ∈ QJ ∧ ∀ p ∈ QJ, ⁅y, p⁆ = 1 ∨ ⁅y, p⁆ = zJ) ↔ y = 1 ∨ y = zJ ∨ y = w0J ∨ y = zJ * w0J := by
  constructor
  · rintro ⟨hy, hc⟩
    obtain ⟨s, hs, rfl⟩ := zTwo_nf hy fun k hk => hc _ (pcJ_mem k)
    interval_cases s
    · exact Or.inl F_zero
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr F_three))
  · rintro (rfl | rfl | rfl | rfl)
    · exact mem_zTwoOf.1 (one_mem VQ)
    · exact mem_zTwoOf.1 zJ_mem_VQ
    · exact mem_zTwoOf.1 w0J_mem_VQ
    · exact mem_zTwoOf.1 (mul_mem zJ_mem_VQ w0J_mem_VQ)

theorem mem_center_QJ {y : J Dt} :
    (y ∈ QJ ∧ ∀ p ∈ QJ, y * p = p * y) ↔ y = 1 ∨ y = zJ := by
  constructor
  · rintro ⟨hy, hc⟩
    have hc' : ∀ p ∈ QJ, ⁅y, p⁆ = 1 ∨ ⁅y, p⁆ = zJ := fun p hp =>
      Or.inl (commutatorElement_eq_one_iff_mul_comm.2 (hc p hp))
    have hw : ¬ (∀ p ∈ QJ, w0J * p = p * w0J) := fun hw0 => by
      have h1 : w0J * pcJ 1 = pcJ 1 * w0J := hw0 (pcJ 1) (pcJ_mem 1)
      have h2 : ⁅w0J, pcJ 1⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 h1
      rw [w0J_comm_pc1] at h2
      exact zJ_ne_one h2
    rcases (mem_zTwo_QJ.1 ⟨hy, hc'⟩) with h | h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · subst h
      exact (hw hc).elim
    · subst h
      refine (hw fun p hp => ?_).elim
      have h1 := hc p hp
      have h2 := zJ_central p hp
      have hzinv : zJ⁻¹ = zJ := inv_eq_of_mul_eq_one_right zJ_sq
      calc w0J * p = zJ * (zJ * w0J * p) := by rw [← mul_assoc, ← mul_assoc, zJ_sq, one_mul]
        _ = zJ * (p * (zJ * w0J)) := by rw [h1]
        _ = p * w0J := by rw [← mul_assoc, ← mul_assoc, h2, mul_assoc p zJ zJ, zJ_sq, mul_one]
  · rintro (rfl | rfl)
    · exact ⟨one_mem _, fun p _ => by rw [one_mul, mul_one]⟩
    · exact ⟨F_mem 1, zJ_central⟩

@[expose] noncomputable def sylT : Subgroup (J Dt) := QJ.map (MulAut.conj hZ).toMonoidHom

theorem mem_sylT {x : J Dt} : x ∈ sylT ↔ ∃ y ∈ QJ, hZ * y * hZ⁻¹ = x := by
  unfold sylT
  rw [Subgroup.mem_map]
  rfl

theorem conj_mem_sylT {y : J Dt} (hy : y ∈ QJ) : hZ * y * hZ⁻¹ ∈ sylT := mem_sylT.2 ⟨y, hy, rfl⟩

theorem card_sylT : Nat.card sylT = 2 ^ 14 := by
  unfold sylT
  have hinj : Function.Injective (MulAut.conj hZ).toMonoidHom := fun x y h =>
    (MulAut.conj hZ).injective h
  rw [Subgroup.card_map_of_injective hinj, card_QJ]

theorem conj_inj {x y : J Dt} : hZ * x * hZ⁻¹ = hZ * y * hZ⁻¹ ↔ x = y :=
  ⟨fun h => mul_left_cancel (mul_right_cancel h), fun h => h ▸ rfl⟩

theorem conj_mul (x y : J Dt) : hZ * (x * y) * hZ⁻¹ = hZ * x * hZ⁻¹ * (hZ * y * hZ⁻¹) := by group

theorem conj_comm (x y : J Dt) : ⁅hZ * x * hZ⁻¹, hZ * y * hZ⁻¹⁆ = hZ * ⁅x, y⁆ * hZ⁻¹ := by
  simp only [commutatorElement_def]
  group

theorem conj_one : hZ * 1 * hZ⁻¹ = 1 := by group

theorem t_eq : wG 13 = hZ * zJ * hZ⁻¹ := hZ_conj.symm

theorem t_mem_sylT : wG 13 ∈ sylT := t_eq ▸ conj_mem_sylT (F_mem 1)

theorem t_sq : wG 13 * wG 13 = 1 := by
  rw [t_eq, ← conj_mul, zJ_sq, conj_one]

theorem t_ne_one : wG 13 ≠ 1 := by
  rw [t_eq, ← conj_one, Ne, conj_inj]
  exact zJ_ne_one

theorem wT_ne_one : wT ≠ 1 := by
  rw [wT, ← conj_one, Ne, conj_inj]
  exact w0J_ne_one

theorem wT_ne_t : wT ≠ wG 13 := by
  rw [wT, t_eq, Ne, conj_inj]
  exact w0J_ne_zJ

theorem t_central : ∀ p ∈ sylT, wG 13 * p = p * wG 13 := fun p hp => by
  obtain ⟨q, hq, rfl⟩ := mem_sylT.1 hp
  rw [t_eq, ← conj_mul, ← conj_mul, zJ_central q hq]

theorem mem_center_sylT {x : J Dt} :
    (x ∈ sylT ∧ ∀ p ∈ sylT, x * p = p * x) ↔ x = 1 ∨ x = wG 13 := by
  constructor
  · rintro ⟨hx, hc⟩
    obtain ⟨y, hy, rfl⟩ := mem_sylT.1 hx
    have hc' : ∀ q ∈ QJ, y * q = q * y := fun q hq => by
      have := hc _ (conj_mem_sylT hq)
      rwa [← conj_mul, ← conj_mul, conj_inj] at this
    rcases mem_center_QJ.1 ⟨hy, hc'⟩ with rfl | rfl
    · exact Or.inl conj_one
    · exact Or.inr t_eq.symm
  · rintro (rfl | rfl)
    · exact ⟨one_mem _, fun p _ => by rw [one_mul, mul_one]⟩
    · exact ⟨t_mem_sylT, t_central⟩

theorem mem_zTwo_sylT {x : J Dt} :
    (x ∈ sylT ∧ ∀ p ∈ sylT, ⁅x, p⁆ = 1 ∨ ⁅x, p⁆ = wG 13) ↔
      x = 1 ∨ x = wG 13 ∨ x = wT ∨ x = wG 13 * wT := by
  have key : ∀ y ∈ QJ, ((∀ p ∈ sylT, ⁅hZ * y * hZ⁻¹, p⁆ = 1 ∨ ⁅hZ * y * hZ⁻¹, p⁆ = wG 13) ↔
      ∀ q ∈ QJ, ⁅y, q⁆ = 1 ∨ ⁅y, q⁆ = zJ) := fun y _ => by
    constructor
    · intro h q hq
      have := h _ (conj_mem_sylT hq)
      rwa [conj_comm, t_eq, ← conj_one, conj_inj, conj_inj] at this
    · intro h p hp
      obtain ⟨q, hq, rfl⟩ := mem_sylT.1 hp
      rw [conj_comm, t_eq, ← conj_one, conj_inj, conj_inj]
      exact h q hq
  constructor
  · rintro ⟨hx, hc⟩
    obtain ⟨y, hy, rfl⟩ := mem_sylT.1 hx
    rcases mem_zTwo_QJ.1 ⟨hy, (key y hy).1 hc⟩ with rfl | rfl | rfl | rfl
    · exact Or.inl conj_one
    · exact Or.inr (Or.inl t_eq.symm)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (by rw [conj_mul, t_eq, wT])))
  · have hmem : ∀ y, y = 1 ∨ y = zJ ∨ y = w0J ∨ y = zJ * w0J →
        hZ * y * hZ⁻¹ ∈ sylT ∧ ∀ p ∈ sylT, ⁅hZ * y * hZ⁻¹, p⁆ = 1 ∨ ⁅hZ * y * hZ⁻¹, p⁆ = wG 13 :=
      fun y hy => by
        obtain ⟨hyQ, hc⟩ := mem_zTwo_QJ.2 hy
        exact ⟨conj_mem_sylT hyQ, (key y hyQ).2 hc⟩
    rintro (rfl | rfl | rfl | rfl)
    · have := hmem 1 (Or.inl rfl)
      rwa [conj_one] at this
    · have := hmem zJ (Or.inr (Or.inl rfl))
      rwa [← t_eq] at this
    · exact hmem w0J (Or.inr (Or.inr (Or.inl rfl)))
    · have := hmem (zJ * w0J) (Or.inr (Or.inr (Or.inr rfl)))
      rwa [conj_mul, ← t_eq] at this

@[expose] noncomputable def VT : Subgroup (J Dt) := zTwoOf sylT (wG 13) t_central t_sq

theorem mem_VT {x : J Dt} : x ∈ VT ↔ x = 1 ∨ x = wG 13 ∨ x = wT ∨ x = wG 13 * wT :=
  mem_zTwoOf.trans mem_zTwo_sylT

theorem gZ_mem_normalizer : gZ ∈ Subgroup.normalizer (VT : Set (J Dt)) := by
  have ht : gZ * wG 13 * gZ⁻¹ ∈ VT := by
    rw [gZ_conj_t]
    exact mem_VT.2 (Or.inr (Or.inr (Or.inl rfl)))
  have hw : gZ * wT * gZ⁻¹ ∈ VT := by
    rw [gZ_conj_w]
    exact mem_VT.2 (Or.inr (Or.inr (Or.inr rfl)))
  have hsub : ∀ u ∈ VT, gZ * u * gZ⁻¹ ∈ VT := by
    intro u hu
    rcases mem_VT.1 hu with rfl | rfl | rfl | rfl
    · rw [mul_one, mul_inv_cancel]
      exact one_mem _
    · exact ht
    · exact hw
    · have e : gZ * (wG 13 * wT) * gZ⁻¹ = gZ * wG 13 * gZ⁻¹ * (gZ * wT * gZ⁻¹) := by group
      rw [e]
      exact mul_mem ht hw
  have hinj : Function.Injective (MulAut.conj gZ).toMonoidHom := (MulAut.conj gZ).injective
  have hle : VT.map (MulAut.conj gZ).toMonoidHom ≤ VT := by
    rintro _ ⟨u, hu, rfl⟩
    exact hsub u hu
  have hcard : Nat.card VT ≤ Nat.card (VT.map (MulAut.conj gZ).toMonoidHom) :=
    (Subgroup.card_map_of_injective hinj).ge
  have hmap : VT.map (MulAut.conj gZ).toMonoidHom = VT := Subgroup.eq_of_le_of_card_ge hle hcard
  rw [Subgroup.mem_normalizer_iff]
  intro u
  refine ⟨hsub u, fun hu => ?_⟩
  rw [← hmap] at hu
  obtain ⟨v, hv, hve⟩ := hu
  change gZ * v * gZ⁻¹ = gZ * u * gZ⁻¹ at hve
  rw [← mul_left_cancel (mul_right_cancel hve)]
  exact hv

theorem ab_ok : WZL 73 = hnAWord.map pcode ++ [2 * 0] ∧ WZL 74 = hnBWord.map pcode ++ [2 * 1] ∧
    ∀ z ∈ hnAWord ++ hnBWord, z ≠ 0 ∧ (z.natAbs = 64 ∨ (z.natAbs ≤ 63 ∧
      ∃ k < 23,
        WZL (75 + k) = [2 * (z.natAbs - 1) + 1, 2 * 13 + 1, 2 * (z.natAbs - 1), 2 * 13])) := by
  decide +kernel

theorem mat_topZ {z : ℤ} (hz : z ≠ 0) (h64 : z.natAbs = 64 ∨ z.natAbs ≤ 63) :
    mat Dt (topZ z) = lm (pcode z) := by
  unfold topZ
  rcases h64 with h | h
  · rw [if_neg (by omega)]
    unfold pcode
    rw [if_pos h]
    by_cases hp : 0 < z
    · rw [if_pos hp, if_pos hp, lm_odd, mat_gZ]
    · rw [if_neg hp, if_neg hp, Nat.add_zero, lm_even, mat_inv_of (by norm_num) mat_gZ]
  · rw [if_pos h]
    exact mat_progZ hz h

theorem word_eq {w : List ℤ} {g k : ℕ} (hk : k < 127) (hg : g < 63)
    (hs : WZL k = w.map pcode ++ [2 * g])
    (hw : ∀ z ∈ w, z ≠ 0 ∧ (z.natAbs = 64 ∨ z.natAbs ≤ 63)) : wordG topZ w = wG g := by
  apply mat_injective Dt
  rw [mat_wordG', mat_wG g hg, ← word_root hk (by omega) hs, List.map_map]
  congr 1
  exact List.map_congr_left fun z hz => mat_topZ (hw z hz).1 (hw z hz).2

theorem a_b_eq : a Dt = wordG topZ hnAWord ∧ b Dt = wordG topZ hnBWord := by
  obtain ⟨ha, hb, hl⟩ := ab_ok
  have hv : ∀ z ∈ hnAWord ++ hnBWord, z ≠ 0 ∧ (z.natAbs = 64 ∨ z.natAbs ≤ 63) :=
    fun z hz => ⟨(hl z hz).1, (hl z hz).2.imp id fun h => h.1⟩
  constructor
  · rw [← wG0]
    exact (word_eq (by norm_num) (by norm_num) ha fun z hz => hv z (List.mem_append_left _ hz)).symm
  · rw [← wG1]
    exact (word_eq (by norm_num) (by norm_num) hb fun z hz =>
      hv z (List.mem_append_right _ hz)).symm

theorem letters_ok : ∀ z ∈ hnAWord ++ hnBWord, z ≠ 0 ∧ (z.natAbs = 64 ∨
    (z.natAbs ≤ 63 ∧ wG (z.natAbs - 1) * wG 13 = wG 13 * wG (z.natAbs - 1))) := by
  intro z hz
  obtain ⟨hz0, h⟩ := ab_ok.2.2 z hz
  refine ⟨hz0, h.imp id fun ⟨h63, k, hk, hs⟩ => ⟨h63, ?_⟩⟩
  have hgj : good ((2 * (z.natAbs - 1) + 1) / 2) ∧ good (2 * (z.natAbs - 1) / 2) := by
    unfold good
    omega
  have h4 := rel4 (by omega) hs hgj.1 (by decide) hgj.2 (by decide)
  rw [elC_odd, elC_odd, elC_even, elC_even, E_wG (by omega), E_wG (by norm_num),
    ← commutatorElement_def, commutatorElement_eq_one_iff_mul_comm] at h4
  exact h4

theorem hn75346_facts : ∃ (T : Subgroup (J Dt)) (w : J Dt) (hc : ∀ p ∈ T, wG 13 * p = p * wG 13)
    (hs : wG 13 * wG 13 = 1), Nat.card T = 2 ^ 14 ∧ wG 13 ∈ T ∧ wG 13 ≠ 1 ∧
      (∀ x, (x ∈ T ∧ ∀ p ∈ T, x * p = p * x) ↔ x = 1 ∨ x = wG 13) ∧
      w ≠ 1 ∧ w ≠ wG 13 ∧
      (∀ x, x ∈ zTwoOf T (wG 13) hc hs ↔ x = 1 ∨ x = wG 13 ∨ x = w ∨ x = wG 13 * w) ∧
      gZ * wG 13 * gZ⁻¹ = w ∧ gZ * w * gZ⁻¹ = wG 13 * w ∧
      gZ ∈ Subgroup.normalizer (zTwoOf T (wG 13) hc hs : Set (J Dt)) ∧
      a Dt = wordG topZ hnAWord ∧ b Dt = wordG topZ hnBWord ∧
      ∀ z ∈ hnAWord ++ hnBWord, z ≠ 0 ∧ (z.natAbs = 64 ∨
        (z.natAbs ≤ 63 ∧ wG (z.natAbs - 1) * wG 13 = wG 13 * wG (z.natAbs - 1))) :=
  ⟨sylT, wT, t_central, t_sq, card_sylT, t_mem_sylT, t_ne_one, fun _ => mem_center_sylT,
    wT_ne_one, wT_ne_t, fun _ => mem_VT, gZ_conj_t, gZ_conj_w, gZ_mem_normalizer, a_b_eq.1,
    a_b_eq.2, letters_ok⟩

end CertificateChecks.KernelHNLocalZ

end
