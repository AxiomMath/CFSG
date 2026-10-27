module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.HNFSetup
public import CFSG.Sporadic.HNSchreier.Faithful
public import Certificates.Kernel.HNF26720.Checks
public import CFSG.Certificates.Kernel.HNF26720Sound
import Certificates.Kernel.HN3166.Seed
import CFSG.Certificates.Kernel.Fam.HNSeed.Checks.K
import Mathlib.Tactic.IntervalCases

public section

namespace CertificateChecks.KernelHNF26720

open CFSG.EvenSporadicStandard.Solomon78 CFSG.Sporadic.HNSchreier CFSG.Sporadic.F5
open CFSG.Sporadic.HNSchreier.Native CFSG.ONSchreier CFSG.ONSchreier.Native
open CFSG.KC.Ord CFSG.KS.Ord CFSG.KC.HNF26720 CFSG.KS.HNF26720 CFSG.KD.HNF26720 Matrix

abbrev Valid (l : ℤ) : Prop := l ≠ 0 ∧ l.natAbs ≤ 2

theorem valid_one : Valid 1 := ⟨by norm_num, by norm_num⟩

theorem valid_xw {w : List ℤ} (hw : ∀ l ∈ w, Valid l) :
    ∀ l ∈ (1 :: w) ++ (1 :: invW w), Valid l := by
  intro l hl
  simp only [List.cons_append, List.mem_cons, List.mem_append, invW, List.mem_map,
    List.mem_reverse] at hl
  rcases hl with rfl | hl | rfl | ⟨m, hm, rfl⟩
  · exact valid_one
  · exact hw l hl
  · exact valid_one
  · have := hw m hm
    exact ⟨by omega, by omega⟩

section Generic

variable {G : Type} [Group G] (ρ : G →* Matrix (Fin 133) (Fin 133) (ZMod 5))

theorem ρ_inv_mul (g : G) : ρ g⁻¹ * ρ g = 1 := by rw [← map_mul, inv_mul_cancel, map_one]

theorem ρ_mul_inv (g : G) : ρ g * ρ g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]

noncomputable def rkG (a : G) (k : ℕ) (y : G) : ℕ := (ρ ((a * y) ^ k) - 1).rank

theorem rk_conj (a : G) (k : ℕ) {c y : G} (hc : c ∈ Subgroup.centralizer ({a} : Set G)) :
    rkG ρ a k (c * y * c⁻¹) = rkG ρ a k y := by
  have hca : c * a = a * c := Subgroup.mem_centralizer_singleton_iff.1 hc
  have e1 : a * (c * y * c⁻¹) = c * (a * y) * c⁻¹ := by
    rw [← mul_assoc, ← mul_assoc, ← hca, mul_assoc c a y]
  have e2 : ρ ((c * (a * y) * c⁻¹) ^ k) - 1 = ρ c * (ρ ((a * y) ^ k) - 1) * ρ c⁻¹ := by
    rw [conj_pow, map_mul, map_mul, mul_sub, sub_mul, mul_one, ρ_mul_inv]
  unfold rkG
  rw [e1, e2, rank_mul_eq_left_of_isUnit_det _ _ (isUnit_det_of_right_inverse (ρ_inv_mul ρ c)),
    rank_mul_eq_right_of_isUnit_det _ _ (isUnit_det_of_right_inverse (ρ_mul_inv ρ c))]

theorem disjoint_of_ranks (a : G) {x y : G} (h : rkG ρ a 1 x ≠ rkG ρ a 1 y ∨ rkG ρ a 2 x ≠ rkG ρ a 2 y) :
    Disjoint (conjOrb (Subgroup.centralizer ({a} : Set G)) x)
      (conjOrb (Subgroup.centralizer ({a} : Set G)) y) := by
  rw [Set.disjoint_left]
  rintro z ⟨c, hc, rfl⟩ ⟨d, hd, hz⟩
  have h1 := rk_conj ρ a 1 hc (y := x)
  have h2 := rk_conj ρ a 2 hc (y := x)
  have h3 := rk_conj ρ a 1 hd (y := y)
  have h4 := rk_conj ρ a 2 hd (y := y)
  rw [hz] at h3 h4
  rcases h with h | h
  · exact h (h1.symm.trans h3)
  · exact h (h2.symm.trans h4)

variable (gs : ℕ → G) (ML : ℤ → Matrix (Fin 133) (Fin 133) (ZMod 5))
  (h1 : ML 1 = ρ (gs 0)) (hm1 : ML (-1) = ρ (gs 0)) (h2 : ML 2 = ρ (gs 1))
  (hm2 : ML (-2) = ρ (gs 1) * ρ (gs 1)) (hA : ρ (gs 0) ^ 2 = 1) (hB : ρ (gs 1) ^ 3 = 1)
include h1 hm1 h2 hm2 hA hB

theorem ml_letter {l : ℤ} (hl : Valid l) : ML l = ρ (letterVal gs l) := by
  have h4 : l = 1 ∨ l = 2 ∨ l = -1 ∨ l = -2 := by omega
  rcases h4 with rfl | rfl | rfl | rfl
  · rw [h1]
    simp [letterVal]
  · rw [h2]
    simp [letterVal]
  · have e : letterVal gs (-1) = (gs 0)⁻¹ := by simp [letterVal]
    rw [hm1, e]
    calc ρ (gs 0) = (ρ (gs 0)⁻¹ * ρ (gs 0)) * ρ (gs 0) := by rw [ρ_inv_mul, one_mul]
      _ = ρ (gs 0)⁻¹ * ρ (gs 0) ^ 2 := by rw [mul_assoc, sq]
      _ = ρ (gs 0)⁻¹ := by rw [hA, mul_one]
  · have e : letterVal gs (-2) = (gs 1)⁻¹ := by simp [letterVal]
    rw [hm2, e]
    calc ρ (gs 1) * ρ (gs 1) = (ρ (gs 1)⁻¹ * ρ (gs 1)) * (ρ (gs 1) * ρ (gs 1)) := by
          rw [ρ_inv_mul, one_mul]
      _ = ρ (gs 1)⁻¹ * ρ (gs 1) ^ 3 := by
          rw [pow_succ, sq]
          simp only [mul_assoc]
      _ = ρ (gs 1)⁻¹ := by rw [hB, mul_one]

theorem ml_word : ∀ w : List ℤ, (∀ l ∈ w, Valid l) → (w.map ML).prod = ρ (wordProd gs w)
  | [], _ => by rw [List.map_nil, List.prod_nil, wordProd_nil, map_one]
  | l :: w, h => by
    rw [List.map_cons, List.prod_cons, ml_letter ρ gs ML h1 hm1 h2 hm2 hA hB (h l List.mem_cons_self),
      ml_word w (fun x hx => h x (List.mem_cons_of_mem _ hx)), wordProd_cons, map_mul]

theorem ml_xw {w : List ℤ} (hw : ∀ l ∈ w, Valid l) :
    (((1 :: w) ++ (1 :: invW w)).map ML).prod = ρ (gs 0 * conjBy (wordProd gs w) (gs 0)) := by
  rw [ml_word ρ gs ML h1 hm1 h2 hm2 hA hB _ (valid_xw hw)]
  have e : invW w = invWord w := rfl
  have e1 : letterVal gs 1 = gs 0 := by simp [letterVal]
  rw [e, wordProd_append, wordProd_cons, wordProd_cons,
    wordProd_invWord gs w (fun l hl => (hw l hl).1), e1, conjBy_def]
  simp only [mul_assoc]

theorem rk_of_ml {w : List ℤ} (hw : ∀ l ∈ w, Valid l) {r s : ℕ}
    (hr : ((((1 :: w) ++ (1 :: invW w)).map ML).prod - 1).rank = r)
    (hs : ((((1 :: w) ++ (1 :: invW w)).map ML).prod ^ 2 - 1).rank = s) :
    rkG ρ (gs 0) 1 (conjBy (wordProd gs w) (gs 0)) = r ∧
      rkG ρ (gs 0) 2 (conjBy (wordProd gs w) (gs 0)) = s := by
  rw [ml_xw ρ gs ML h1 hm1 h2 hm2 hA hB hw] at hr hs
  unfold rkG
  rw [pow_one, map_pow]
  exact ⟨hr, hs⟩

theorem mem_centralizer_of_letters (hρ : Function.Injective ρ) {w : List ℤ} (hw : ∀ l ∈ w, Valid l)
    (h : ((1 :: w).map ML).prod = ((w ++ [1]).map ML).prod) :
    wordProd gs w ∈ Subgroup.centralizer ({gs 0} : Set G) := by
  have hv1 : ∀ l ∈ 1 :: w, Valid l := by
    intro l hl
    rcases List.mem_cons.1 hl with rfl | hl
    · exact valid_one
    · exact hw l hl
  have hv2 : ∀ l ∈ w ++ [1], Valid l := by
    intro l hl
    rcases List.mem_append.1 hl with hl | hl
    · exact hw l hl
    · rw [List.mem_singleton.1 hl]
      exact valid_one
  rw [ml_word ρ gs ML h1 hm1 h2 hm2 hA hB _ hv1, ml_word ρ gs ML h1 hm1 h2 hm2 hA hB _ hv2] at h
  have e1 : letterVal gs 1 = gs 0 := by simp [letterVal]
  rw [wordProd_cons, wordProd_append, e1, wordProd_cons, wordProd_nil, mul_one, e1] at h
  exact Subgroup.mem_centralizer_singleton_iff.2 (hρ h).symm

end Generic

@[expose] noncomputable def ρJ : ↥JH →* Matrix (Fin 133) (Fin 133) (ZMod 5) where
  toFun := matJ
  map_one' := rfl
  map_mul' _ _ := rfl

theorem ρJ_injective : Function.Injective ρJ := fun _ _ h => matJ_injective h

theorem cA : Canon 5 133 13 (CFSG.KD.FamHNSeed.RW 1) :=
  validM_canon (d := 133) (S := 1729) CFSG.KD.FamHNSeed.consts KernelHN.s_v1

theorem cB : Canon 5 133 13 (CFSG.KD.FamHNSeed.RW 2) :=
  validM_canon (d := 133) (S := 1729) CFSG.KD.FamHNSeed.consts KernelHN.s_v2

theorem cBi : Canon 5 133 13 Bi := (mul_sound CFSG.KD.FamHNSeed.consts cB cB).1

theorem mA_om : (mA hnsData : Matrix (Fin 133) (Fin 133) (ZMod 5)) =
    CFSG.KS.HNLocal.OM (CFSG.KD.FamHNSeed.RW 1) :=
  KernelHN.s_mA

theorem mB_om : (mB hnsData : Matrix (Fin 133) (Fin 133) (ZMod 5)) =
    CFSG.KS.HNLocal.OM (CFSG.KD.FamHNSeed.RW 2) :=
  KernelHN.s_mB

theorem hnfAB_zero : hnfAB 0 = aJ := by simp [hnfAB]

theorem hnfAB_one : hnfAB 1 = bJ := by simp [hnfAB]

theorem ρJ_apply (g : ↥JH) : ρJ g = matJ g := rfl

theorem omA_sq : CFSG.KS.HNLocal.OM (CFSG.KD.FamHNSeed.RW 1) ^ 2 = 1 := by
  have h := KernelHN.mA_sq
  rw [KernelHN.s_mA] at h
  exact h

theorem omB_cube : CFSG.KS.HNLocal.OM (CFSG.KD.FamHNSeed.RW 2) ^ 3 = 1 := by
  have h := KernelHN.mB_cube
  rw [KernelHN.s_mB] at h
  exact h

theorem matJ_aJ : matJ aJ = CFSG.KS.HNLocal.OM (CFSG.KD.FamHNSeed.RW 1) := by
  have hsq : (mA hnsData : Matrix (Fin 133) (Fin 133) (ZMod 5)) ^ 2 = 1 := by
    rw [mA_om]
    exact omA_sq
  have hd : (mA hnsData).det ≠ 0 := det_ne_zero_of_pow_eq_one' (by norm_num) hsq
  rw [matJ, mat_a' hd, mA_om]

theorem matJ_bJ : matJ bJ = CFSG.KS.HNLocal.OM (CFSG.KD.FamHNSeed.RW 2) := by
  have hcu : (mB hnsData : Matrix (Fin 133) (Fin 133) (ZMod 5)) ^ 3 = 1 := by
    rw [mB_om]
    exact omB_cube
  have hd : (mB hnsData).det ≠ 0 := det_ne_zero_of_pow_eq_one' (by norm_num) hcu
  rw [matJ, mat_b' hd, mB_om]

theorem om_A : ρJ (hnfAB 0) = CFSG.KS.HNLocal.OM (CFSG.KD.FamHNSeed.RW 1) := by
  rw [hnfAB_zero, ρJ_apply, matJ_aJ]

theorem om_B : ρJ (hnfAB 1) = CFSG.KS.HNLocal.OM (CFSG.KD.FamHNSeed.RW 2) := by
  rw [hnfAB_one, ρJ_apply, matJ_bJ]

noncomputable abbrev MLJ (l : ℤ) : Matrix (Fin 133) (Fin 133) (ZMod 5) :=
  CFSG.KS.HNLocal.OM (ltr (CFSG.KD.FamHNSeed.RW 1) (CFSG.KD.FamHNSeed.RW 2) Bi l)

theorem mlj1 : MLJ 1 = ρJ (hnfAB 0) := by
  rw [om_A, MLJ, ltr_one]

theorem mljm1 : MLJ (-1) = ρJ (hnfAB 0) := by
  rw [om_A, MLJ, ltr_neg_one]

theorem mlj2 : MLJ 2 = ρJ (hnfAB 1) := by
  rw [om_B, MLJ, ltr_two]

theorem mljm2 : MLJ (-2) = ρJ (hnfAB 1) * ρJ (hnfAB 1) := by
  rw [om_B, MLJ, ltr_neg_two]
  exact (mul_sound CFSG.KD.FamHNSeed.consts cB cB).2

theorem hA2 : ρJ (hnfAB 0) ^ 2 = 1 := by
  rw [om_A]
  exact omA_sq

theorem hB3 : ρJ (hnfAB 1) ^ 3 = 1 := by
  rw [om_B]
  exact omB_cube

theorem valid_of {w : List ℤ} (hw : plettersOK 2 w = true) : ∀ l ∈ w, Valid l :=
  plettersOK_iff.1 hw

theorem pairs : ∀ i < 9, pairW hnfRepWords[i]! i = true := by
  intro i hi
  interval_cases i
  exacts [p0, p1, p2, p3, p4, p5, p6, p7, p8]

theorem ranks (i : Fin 9) :
    ((((1 :: hnfRepWords[i.val]!) ++ (1 :: invW hnfRepWords[i.val]!)).map MLJ).prod - 1).rank =
        KS (2 * i.val) ∧
      ((((1 :: hnfRepWords[i.val]!) ++ (1 :: invW hnfRepWords[i.val]!)).map MLJ).prod ^ 2 -
        1).rank = KS (2 * i.val + 1) := by
  have hs := pair_sound CFSG.KD.FamHNSeed.consts cA cB cBi (pairs i.val i.isLt)
  rw [xw, (wprod_sound CFSG.KD.FamHNSeed.consts cA cB cBi _).2] at hs
  exact hs

theorem dist_spec (i j : Fin 9) (hij : i ≠ j) :
    KS (2 * i.val) ≠ KS (2 * j.val) ∨ KS (2 * i.val + 1) ≠ KS (2 * j.val + 1) := by
  have h := dist
  unfold distOK at h
  rw [List.all_eq_true] at h
  have h2 := h i.val (List.mem_range.2 i.isLt)
  rw [List.all_eq_true] at h2
  have h3 := h2 j.val (List.mem_range.2 j.isLt)
  have hne : (i.val == j.val) = false := by
    rw [beq_eq_false_iff_ne]
    exact fun e => hij (Fin.ext e)
  rw [hne, Bool.false_or] at h3
  rcases Bool.or_eq_true_iff.1 h3 with h4 | h4
  · left
    intro e
    rw [e, beq_self_eq_true] at h4
    exact absurd h4 (by decide)
  · right
    intro e
    rw [e, beq_self_eq_true] at h4
    exact absurd h4 (by decide)

theorem comm_letters (w : List ℤ) (h : commW w = true) :
    ((1 :: w).map MLJ).prod = ((w ++ [1]).map MLJ).prod :=
  comm_sound CFSG.KD.FamHNSeed.consts cA cB cBi h

theorem g_mem {w : List ℤ} (hw : plettersOK 2 w = true) (h : commW w = true) :
    wordProd hnfAB w ∈ Subgroup.centralizer ({hnfAB 0} : Set ↥JH) :=
  mem_centralizer_of_letters ρJ hnfAB MLJ mlj1 mljm1 mlj2 mljm2 hA2 hB3 ρJ_injective (valid_of hw)
    (comm_letters w h)

theorem rep_disjoint (i j : Fin 9) (hij : i ≠ j) :
    Disjoint (conjOrb (Subgroup.centralizer ({hnfAB 0} : Set ↥JH))
        (conjBy (wordProd hnfAB hnfRepWords[i.val]!) (hnfAB 0)))
      (conjOrb (Subgroup.centralizer ({hnfAB 0} : Set ↥JH))
        (conjBy (wordProd hnfAB hnfRepWords[j.val]!) (hnfAB 0))) := by
  have hi := rk_of_ml ρJ hnfAB MLJ mlj1 mljm1 mlj2 mljm2 hA2 hB3
    (valid_of (hnfRepWords_ok i.val i.isLt)) (ranks i).1 (ranks i).2
  have hj := rk_of_ml ρJ hnfAB MLJ mlj1 mljm1 mlj2 mljm2 hA2 hB3
    (valid_of (hnfRepWords_ok j.val j.isLt)) (ranks j).1 (ranks j).2
  apply disjoint_of_ranks ρJ
  rw [hi.1, hi.2, hj.1, hj.2]
  exact dist_spec i j hij

theorem facts : hnfG1 ∈ Subgroup.centralizer ({aJ} : Set ↥JH) ∧
    hnfG2 ∈ Subgroup.centralizer ({aJ} : Set ↥JH) ∧
    ∀ i j : Fin 9, i ≠ j →
      Disjoint (conjOrb (Subgroup.centralizer ({aJ} : Set ↥JH)) (hnfRep hnfRepWords[i.val]!))
        (conjOrb (Subgroup.centralizer ({aJ} : Set ↥JH)) (hnfRep hnfRepWords[j.val]!)) := by
  have e : hnfAB 0 = aJ := hnfAB_zero
  have h1 := g_mem hnfW1_ok c1
  have h2 := g_mem hnfW2_ok c2
  have h3 := rep_disjoint
  rw [e] at h1 h2 h3
  exact ⟨h1, h2, h3⟩

end CertificateChecks.KernelHNF26720

end
