module

public import Certificates.Kernel.Sporadic.Fi24Sev.SevenB
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24SevenFacts
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3ThreeKit
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.CommutingPair
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalThreeSporadicRank
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Core
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Reduction
public import CFSG.LocalAnalysis.GLTheoremB.QuotientTools

public section

namespace CFSG.KD.Fi24Sev.Three

open CFSG.HardMathSupport.Solomon.Coordinator.YS08 (fixS mem_fixS card_fixS_conj_inv)

section Generic

variable {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Fintype Ω] [DecidableEq Ω]

theorem fixS_inv (g : G) : (fixS g⁻¹ : Finset Ω) = fixS g := by
  ext i
  rw [mem_fixS, mem_fixS, inv_smul_eq_iff, eq_comm]

theorem card_fixS_sq {g : G} (h : g ^ 3 = 1) :
    (fixS (g ^ 2) : Finset Ω).card = (fixS g : Finset Ω).card := by
  have : g ^ 2 = g⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← pow_succ, h])
  rw [this, fixS_inv]

theorem ne_one_of_card_fixS {g : G} {n : ℕ} (h : (fixS g : Finset Ω).card = n)
    (hn : n ≠ Fintype.card Ω) : g ≠ 1 := by
  rintro rfl
  apply hn
  rw [← h]
  simp [fixS]

theorem conj_eq_one {g x : G} (h : g⁻¹ * x * g = 1) : x = 1 := by
  calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
    _ = 1 := by rw [h]; group

theorem three_of_pair {y u v : G} {a b : ℕ} (hcard : Nat.card (Subgroup.centralizer ({y} : Set G)) = 17640)
    (hu3 : u ^ 3 = 1) (hv3 : v ^ 3 = 1) (huv : u * v = v * u) (huy : u * y = y * u)
    (hvy : v * y = y * v) (hu1 : u ≠ 1) (hv1 : v ≠ 1) (hvu : v ≠ u) (hvuu : v ≠ u * u)
    (fu : (fixS u : Finset Ω).card = b) (fv : (fixS v : Finset Ω).card = b)
    (fuv : (fixS (u * v) : Finset Ω).card = a) (fuv2 : (fixS (u * v * v) : Finset Ω).card = a)
    (x : G) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) (hxy : x * y = y * x) :
    (fixS x : Finset Ω).card = a ∨ (fixS x : Finset Ω).card = b := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C := Subgroup.centralizer ({y} : Set G) with hC
  have memC : ∀ g : G, g * y = y * g → g ∈ C := fun g hg =>
    Subgroup.mem_centralizer_singleton_iff.2 hg
  let u' : C := ⟨u, memC _ huy⟩
  let v' : C := ⟨v, memC _ hvy⟩
  have hc' : Commute u' v' := Subtype.ext huv
  have hu3' : u' ^ 3 = 1 := Subtype.ext hu3
  have hv3' : v' ^ 3 = 1 := Subtype.ext hv3
  have hK : Nat.card (Subgroup.closure ({u', v'} : Set C)) = 3 ^ 2 := by
    refine CFSG.HardMathSupport.Timmesfeld.SporadicBalance.CommutingPair.card_closure_pair_eq_sq
      hc' hu3' hv3' (fun h => hu1 (congrArg Subtype.val h)) (fun k hk h => ?_)
      (by rw [hcard]; norm_num)
    interval_cases k
    · rw [pow_zero] at h
      exact hv1 (congrArg Subtype.val h)
    · rw [pow_one] at h
      exact hvu (congrArg Subtype.val h)
    · rw [pow_two] at h
      exact hvuu (congrArg Subtype.val h)
  have hfac : (Nat.card (⊤ : Subgroup C)).factorization 3 = 2 := by
    rw [Subgroup.card_top, hcard, show (17640 : ℕ) = 3 ^ 2 * 1960 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  let x' : C := ⟨x, memC x hxy⟩
  have hx'o : orderOf x' = 3 :=
    orderOf_eq_prime (Subtype.ext hx3) (fun h => hx1 (congrArg Subtype.val h))
  obtain ⟨g, -, hg⟩ := CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3T.exists_conj_mem_of_full
    le_top (by rw [hK, hfac]) (Subgroup.mem_top x') hx'o
  obtain ⟨i, hi, j, hj, hw⟩ :=
    CFSG.HardMathSupport.Timmesfeld.SporadicBalance.CommutingPair.exists_pow_mul_pow_of_mem
      (by norm_num) hc' hu3' hv3' hg
  have hw' : (g : G)⁻¹ * x * g = u ^ i * v ^ j := congrArg Subtype.val hw
  rw [← card_fixS_conj_inv (g : G) x, hw']
  have hcomm : Commute u v := huv
  have huv3 : (u * v) ^ 3 = 1 := by rw [hcomm.mul_pow, hu3, hv3, mul_one]
  have huvv3 : (u * v * v) ^ 3 = 1 := by
    rw [mul_assoc, (hcomm.mul_right hcomm).mul_pow, hu3, (Commute.refl v).mul_pow, hv3, mul_one,
      one_mul]
  interval_cases i <;> interval_cases j
  · exact absurd (conj_eq_one (by rw [hw']; simp)) hx1
  · right; simpa using fv
  · right; rw [pow_zero, one_mul, card_fixS_sq hv3]; exact fv
  · right; simpa using fu
  · left; simpa using fuv
  · left
    have : u ^ 1 * v ^ 2 = u * v * v := by rw [pow_one, pow_two, mul_assoc]
    rw [this]; exact fuv2
  · right; rw [pow_zero, mul_one, card_fixS_sq hu3]; exact fu
  · left
    have : u ^ 2 * v ^ 1 = (u * v * v) ^ 2 := by
      rw [mul_assoc, (hcomm.mul_right hcomm).mul_pow, (Commute.refl v).mul_pow, ← pow_add,
        show v ^ (2 + 2) = v ^ 3 * v by rw [← pow_succ], hv3, one_mul, pow_one]
    rw [this, card_fixS_sq huvv3]; exact fuv2
  · left
    have : u ^ 2 * v ^ 2 = (u * v) ^ 2 := by rw [hcomm.mul_pow]
    rw [this, card_fixS_sq huv3]; exact fuv

theorem three_of_cyclic {c w : G} {a : ℕ}
    (hcard : Nat.card (Subgroup.centralizer ({c} : Set G)) = 2058)
    (hw3 : w ^ 3 = 1) (hw1 : w ≠ 1) (hwc : w * c = c * w) (fw : (fixS w : Finset Ω).card = a)
    (x : G) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) (hxc : x * c = c * x) :
    (fixS x : Finset Ω).card = a := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C := Subgroup.centralizer ({c} : Set G) with hC
  have memC : ∀ g : G, g * c = c * g → g ∈ C := fun g hg =>
    Subgroup.mem_centralizer_singleton_iff.2 hg
  let w' : C := ⟨w, memC _ hwc⟩
  have hw'o : orderOf w' = 3 :=
    orderOf_eq_prime (Subtype.ext hw3) (fun h => hw1 (congrArg Subtype.val h))
  have hK : Nat.card (Subgroup.zpowers w') = 3 ^ 1 := by rw [Nat.card_zpowers, hw'o, pow_one]
  have hfac : (Nat.card (⊤ : Subgroup C)).factorization 3 = 1 := by
    rw [Subgroup.card_top, hcard, show (2058 : ℕ) = 3 ^ 1 * 686 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  let x' : C := ⟨x, memC x hxc⟩
  have hx'o : orderOf x' = 3 :=
    orderOf_eq_prime (Subtype.ext hx3) (fun h => hx1 (congrArg Subtype.val h))
  obtain ⟨g, -, hg⟩ := CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3T.exists_conj_mem_of_full
    le_top (by rw [hK, hfac]) (Subgroup.mem_top x') hx'o
  obtain ⟨n, hn⟩ := mem_powers_iff_mem_zpowers.2 hg
  have hw3' : w' ^ 3 = 1 := Subtype.ext hw3
  replace hn : w' ^ n = g⁻¹ * x' * g := hn
  rw [pow_eq_pow_mod n hw3'] at hn
  have hw' : (g : G)⁻¹ * x * g = w ^ (n % 3) := (congrArg Subtype.val hn).symm
  rw [← card_fixS_conj_inv (g : G) x, hw']
  have hn3 : n % 3 < 3 := Nat.mod_lt _ (by norm_num)
  interval_cases h : n % 3
  · exact absurd (conj_eq_one (by rw [hw', pow_zero])) hx1
  · rw [pow_one]; exact fw
  · rw [card_fixS_sq hw3]; exact fw

theorem no_root {r : G} (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1) (hpow : ∀ g : G, g ^ 49 = 1 → g ^ 7 = 1)
    (g : G) : g ^ 7 ≠ r := by
  intro hg
  have h49 : g ^ 49 = 1 := by rw [show 49 = 7 * 7 by norm_num, pow_mul, hg, hr7]
  exact hr1 (hg ▸ hpow g h49)

theorem comm_pow_seven {x y c : G} (hx7 : x ^ 7 = 1) (hy7 : y ^ 7 = 1)
    (hc : c = x * y * x ^ 6 * y ^ 6) (hcy : c * y = y * c) : c ^ 7 = 1 := by
  have h6 : x ^ 6 = x⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← pow_succ, hx7])
  have h6' : y ^ 6 = y⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← pow_succ, hy7])
  have hxy : x * y * x⁻¹ = c * y := by rw [hc, h6, h6']; group
  have hcy' : Commute c y := hcy
  have key : x * y ^ 7 * x⁻¹ = c ^ 7 * y ^ 7 := by
    rw [← hcy'.mul_pow 7, ← hxy, conj_pow]
  rw [hy7, mul_one, mul_inv_cancel, mul_one] at key
  exact key.symm

end Generic

open CFSG.Sporadic.Fi24 (J)
open CFSG.KD.Fi24ThreeO.Group CFSG.KD.Fi24Sev.SevenB
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24SevenNative (fi24SevenData)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


theorem finite_J : Finite J :=
  Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Fi24.card_J]; norm_num)

theorem g7_iy : CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Seven.g7 fi24SevenData.iy =
    sev 66 := rfl

theorem g7_ic : CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Seven.g7 fi24SevenData.ic =
    sev 67 := rfl

theorem centFacts (hB : Bridge) (hpow : ∀ g : J, g ^ 49 = 1 → g ^ 7 = 1) :
    CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Seven.CentFacts := by
  have := finite_J
  obtain ⟨hx7, hy7, hc, -, hcy, hc1⟩ := cube_facts hB
  obtain ⟨hu3, hv3, huv, huy, hvy, hu1, hv1, hvu, hvuu, -, -, -, -, -, -, -, -, hw3, hw1, hwc, -⟩ :=
    elt_facts hB
  obtain ⟨fu, fv, fuv, fuv2, fw, fy, fc⟩ := fix_facts hB
  have hy1 : sev 66 ≠ 1 := ne_one_of_card_fixS fy (by simp)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [g7_iy]
    exact three_of_pair (CFSG.KD.Fi24Sev.Seven.card_centralizer_y hB) hu3 hv3 huv huy hvy hu1 hv1
      hvu hvuu fu fv fuv fuv2
  · rw [g7_ic]
    exact three_of_cyclic (CFSG.KD.Fi24Sev.Seven.card_centralizer_c hB) hw3 hw1 hwc fw
  · rw [g7_iy]
    exact no_root hy7 hy1 hpow
  · rw [g7_ic]
    exact no_root (comm_pow_seven hx7 hy7 hc hcy) hc1 hpow
  · rw [g7_iy]
    exact fy
  · rw [g7_ic]
    exact fc

end CFSG.KD.Fi24Sev.Three

end
