module

public import Certificates.Kernel.StdOdd.Cent7.Checks
public import Certificates.Kernel.StdOdd.Cent7.Sound
public import Certificates.Kernel.StdOdd.Cent7.Cent
public import CFSG.Monster.Existence.StdOdd.Cert.Sylow57
public import CFSG.Monster.Existence.StdOdd.Cert.Cent7A
public import CFSG.Monster.Existence.StdOdd.Cert.Cent7B
import CFSG.Monster.Existence.StdOdd.Cert.Sylow57Data
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

namespace CFSG.KD.StdOdd.Cent7

open CFSG.KC.Misc CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc.E6Std CFSG.KD.Misc.E6Std CFSG.KD.StdOdd.Reps
  CFSG.KD.StdOdd.Sylow57 CFSG.Monster.Existence.StdOdd CFSG.Monster.Existence.StdOdd.Cert
  CFSG.LieType.Chevalley.C2E6Overlap CFSG.LieType.Chevalley.C2E6Std.MatrixModel

set_option maxRecDepth 100000

theorem ch17104lt : Nat.blt 192 (lenN S7.V) = true := by quickRfl

theorem ch17104lt' : Nat.blt 87 (lenN S7.V) = true := by quickRfl


@[expose] def RepR (N : ℕ) (g : Rgrp) : Prop := Rep N (rgrpMat g)

theorem repR_mul {a b : ℕ} {x y : Rgrp} (ha : RepR a x) (hb : RepR b y) : RepR (mulB a b) (x * y) := by
  unfold RepR at *
  rw [map_mul]
  exact rep_mulB ha hb

theorem repR_one : RepR oneB 1 := by
  unfold RepR
  rw [map_one]
  exact rep_oneB

theorem repR_inj {a b : ℕ} {x y : Rgrp} (ha : RepR a x) (hb : RepR b y) : a = b ↔ x = y :=
  (eq_iff_of_rep ha hb).trans rgrpMat_injective.eq_iff

@[expose] noncomputable def lettersOf (a a' b b' : Rgrp) (i : ℕ) : Rgrp := [a, a', b, b'].getD i 1

theorem repR_letters {la la' lb lb' : ℕ} {a a' b b' : Rgrp} (ha : RepR la a) (ha' : RepR la' a')
    (hb : RepR lb b) (hb' : RepR lb' b') :
    ∀ i < 4, RepR (nthV [la, la', lb, lb'] i) (lettersOf a a' b b' i) := by
  intro i hi
  interval_cases i
  · exact ha
  · exact ha'
  · exact hb
  · exact hb'

theorem centFacts_of_letters {s a a' b b' : Rgrp} {ls tw : List ℕ} {te a2 n : ℕ}
    {qws : List (List ℕ × ℕ)} {qsteps steps : List (ℕ × ℕ)} {i1 i2 : ℕ}
    (hs7 : orderOf s = 7)
    (hC : Nat.card (Subgroup.centralizer ({s} : Set Rgrp)) = 2 ^ a2 * (7 * n)) (hodd : Odd n)
    (hX : ∀ i < 4, RepR (nthV ls i) (lettersOf a a' b b' i))
    (haC : a ∈ Subgroup.centralizer ({s} : Set Rgrp))
    (hbC : b ∈ Subgroup.centralizer ({s} : Set Rgrp))
    (hn : 1 + steps.length = n) (hq : 1 + qsteps.length = 2 ^ a2)
    (h : invClassK ls tw te qws qsteps steps i1 i2 = true) :
    (∀ r ∈ Subgroup.centralizer ({s} : Set Rgrp), orderOf r ≠ 6) ∧
      ∀ N : Subgroup Rgrp, N ≤ Subgroup.centralizer ({s} : Set Rgrp) →
        (∀ c ∈ Subgroup.centralizer ({s} : Set Rgrp), ∀ x ∈ N, c * x * c⁻¹ ∈ N) →
        Nat.Coprime 7 (Nat.card N) → N = ⊥ := by
  have : Finite Rgrp := rgrp_finite
  obtain ⟨t, htK, ht2, ht1, hnc, ⟨Q, hQK, hQt, hQ, hinv⟩, g₁, hg₁, g₂, hg₂, h7⟩ :=
    invClassK_sound RepR repR_mul repR_one repR_inj hX h
  have hK : Subgroup.closure {lettersOf a a' b b' 0, lettersOf a a' b b' 2} ≤
      Subgroup.centralizer ({s} : Set Rgrp) := by
    rw [Subgroup.closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨haC, hbC⟩
  refine centFacts_of_invClass hs7 hC hodd hK ⟨t, htK, ht2, ht1, ?_, ⟨Q, hQK, hQt, ?_, hinv⟩,
    g₁, hg₁, g₂, hg₂, h7⟩
  · rw [← hn]
    exact hnc
  · rw [hQ, hq]

theorem centFacts_rep7B_K :
    (∀ r ∈ Subgroup.centralizer ({rep7B} : Set Rgrp), orderOf r ≠ 6) ∧
      ∀ N : Subgroup Rgrp, N ≤ Subgroup.centralizer ({rep7B} : Set Rgrp) →
        (∀ c ∈ Subgroup.centralizer ({rep7B} : Set Rgrp), ∀ x ∈ N, c * x * c⁻¹ ∈ N) →
        Nat.Coprime 7 (Nat.card N) → N = ⊥ := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have : Finite Rgrp := rgrp_finite
  have hx : rgrpMat rep7B = toMat (Native.wordMat nativeAB.1 nativeAB.2 repWord7B) :=
    rgrpMat_repOf repWord7B
  have hRx : RepR x7 rep7B := by
    unfold RepR
    rw [hx, repWord7B, e7B]
    exact rep_word b7B 4
  have hzM := rgrpMat_rgrpSlp sylow7Prog sylow7Z
  set z := (rgrpSlp sylow7Prog).getD sylow7Z 1 with hzdef
  obtain ⟨-, hxz, -, -⟩ := sylowFusionCheck_sound (p := 7) (x := rep7B) (y := z) hx hzM
    orderOf_rep7B sylow7
  have hRz : RepR z7 z := by
    unfold RepR
    rw [hzM]
    exact rep_vals S7.v0 S7.v1 S7.lines S7.len S7.zLt
  have hRd : RepR dB ((rgrpSlp sylow7Prog).getD 87 1) := by
    unfold RepR
    rw [rgrpMat_rgrpSlp sylow7Prog 87]
    exact rep_vals S7.v0 S7.v1 S7.lines S7.len ch17104lt'
  set d := (rgrpSlp sylow7Prog).getD 87 1 with hddef
  have hRl : RepR lB (d ^ 11 * rep7B * d) :=
    repR_mul (repR_mul (powB_sound RepR repR_mul repR_one hRd 11) hRx) hRd
  have hlC : d ^ 11 * rep7B * d ∈ Subgroup.centralizer ({rep7B} : Set Rgrp) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hc := ch17104zB
    rw [letB_eq', Nat.beq_eq] at hc
    exact (repR_inj (repR_mul hRl hRx) (repR_mul hRx hRl)).1 hc.symm
  have hzC : z ∈ Subgroup.centralizer ({rep7B} : Set Rgrp) :=
    Subgroup.mem_centralizer_singleton_iff.2 hxz.eq.symm
  exact centFacts_of_letters (n := 21) (a2 := 3) orderOf_rep7B
    (by rw [card_centralizer_rep7B]; norm_num) ⟨10, rfl⟩
    (repR_letters hRz (powB_sound RepR repR_mul repR_one hRz 6) hRl
      (powB_sound RepR repR_mul repR_one hRl 6)) hzC hlC rfl rfl ch17104B

theorem centFacts_rep7A_K :
    (∀ r ∈ Subgroup.centralizer ({rep7A} : Set Rgrp), orderOf r ≠ 6) ∧
      ∀ N : Subgroup Rgrp, N ≤ Subgroup.centralizer ({rep7A} : Set Rgrp) →
        (∀ c ∈ Subgroup.centralizer ({rep7A} : Set Rgrp), ∀ x ∈ N, c * x * c⁻¹ ∈ N) →
        Nat.Coprime 7 (Nat.card N) → N = ⊥ := by
  have : Finite Rgrp := rgrp_finite
  have hx : rgrpMat rep7B = toMat (Native.wordMat nativeAB.1 nativeAB.2 repWord7B) :=
    rgrpMat_repOf repWord7B
  have hRx : RepR x7 rep7B := by
    unfold RepR
    rw [hx, repWord7B, e7B]
    exact rep_word b7B 4
  have hxa : rgrpMat rep7A = toMat (Native.wordMat nativeAB.1 nativeAB.2 repWord7A) :=
    rgrpMat_repOf repWord7A
  have hRxa : RepR xa7 rep7A := by
    unfold RepR
    rw [hxa, repWord7A, e7A]
    exact rep_word b7A 5
  have hgM : rgrpMat (repOf b7A) = toMat (Native.wordMat nativeAB.1 nativeAB.2 b7A) :=
    rgrpMat_repOf b7A
  have hRg : RepR gA (repOf b7A) := by
    unfold RepR
    rw [hgM]
    exact rep_wordB rep_A rep_B b7A
  have hx5 : rep7A = repOf b7A ^ 5 := by
    apply rgrpMat_injective
    rw [hxa, map_pow, hgM, repWord7A, e7A, toMat_wordPow]
  have hRy : RepR y5A (repOf b7A ^ 7) := powB_sound RepR repR_mul repR_one hRg 7
  have hyC : repOf b7A ^ 7 ∈ Subgroup.centralizer ({rep7A} : Set Rgrp) := by
    rw [Subgroup.mem_centralizer_singleton_iff, hx5]
    exact (Commute.pow_pow_self (repOf b7A) 7 5).eq
  have hRc : RepR cA ((rgrpSlp sylow7Prog).getD 192 1) := by
    unfold RepR
    rw [rgrpMat_rgrpSlp sylow7Prog 192]
    exact rep_vals S7.v0 S7.v1 S7.lines S7.len ch17104lt
  set c := (rgrpSlp sylow7Prog).getD 192 1 with hcdef
  have hRzp : RepR zpA (c ^ 23 * rep7B * c) :=
    repR_mul (repR_mul (powB_sound RepR repR_mul repR_one hRc 23) hRx) hRc
  have hzpC : c ^ 23 * rep7B * c ∈ Subgroup.centralizer ({rep7A} : Set Rgrp) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hc := ch17104zA
    rw [letB_eq', Nat.beq_eq] at hc
    exact (repR_inj (repR_mul hRzp hRxa) (repR_mul hRxa hRzp)).1 hc.symm
  exact centFacts_of_letters (n := 315) (a2 := 6) orderOf_rep7A
    (by rw [card_centralizer_rep7A]; norm_num) ⟨157, rfl⟩
    (repR_letters hRy (powB_sound RepR repR_mul repR_one hRy 4) hRzp
      (powB_sound RepR repR_mul repR_one hRzp 6)) hyC hzpC rfl rfl ch17104A

end CFSG.KD.StdOdd.Cent7

end
