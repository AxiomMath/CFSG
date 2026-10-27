module

public import CFSG.RankThree.PartOne.S11c.J4Rep
public import CFSG.RankThree.PartOne.S11c.J4LocalRank
public import CFSG.Sporadic.Schreier.J4SOuter
public import CFSG.Sporadic.Schreier.J4SCheck
public import CFSG.RankThree.PartOne.S11c.J4RankInputs
public import Certificates.Kernel.SporSch.J4S.Eta
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4F2

open CFSG.RankThree.PartOne CFSG.Sporadic.J4Schreier CFSG.KS.SporSch.J4B CFSG.KC.J4Q CFSG.KD.J4Q
open CertificateChecks.KernelSporSch.J4Eta

private theorem foldr_testBit (X : Array Nat) (hX : ∀ i, X.getD i 0 < 2 ^ 128) {i j : Nat}
    (hj : j < 128) : ∀ L : List Nat,
    (L.foldr (fun k acc => Nat.lor (Nat.shiftLeft (X.getD k 0) (128 * k)) acc) 0).testBit
      (128 * i + j) = (decide (i ∈ L) && (X.getD i 0).testBit j)
  | [] => by simp
  | k :: L => by
    rw [List.foldr_cons, Nat.lor_eq, Nat.testBit_or, foldr_testBit X hX hj L, Nat.shiftLeft_eq',
      Nat.testBit_shiftLeft]
    by_cases hk : k = i
    · subst hk
      have e : 128 * k + j - 128 * k = j := by omega
      simp [e]
    · have hb : (decide (128 * i + j ≥ 128 * k) && (X.getD k 0).testBit (128 * i + j - 128 * k))
          = false := by
        by_cases hge : 128 * i + j ≥ 128 * k
        · have hki : k < i := by omega
          have h2 : 128 ≤ 128 * i + j - 128 * k := by omega
          have : (X.getD k 0).testBit (128 * i + j - 128 * k) = false :=
            Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (hX k) (Nat.pow_le_pow_right (by omega) h2))
          rw [this, Bool.and_false]
        · simp [hge]
      rw [hb, Bool.false_or]
      have hne : i ≠ k := fun h => hk h.symm
      simp [hne]

theorem encN_testBit {X : Array Nat} (hX : WfN X) {i j : Nat} (hi : i < 112) (hj : j < 112) :
    (encN X).testBit (128 * i + j) = (X[i]?.getD 0).testBit j := by
  have hrow : ∀ k, X.getD k 0 < 2 ^ 128 := by
    intro k
    by_cases hk : k < X.size
    · have h := hX.2 k (by rw [← hX.1]; exact hk)
      rw [getElem!_pos X k hk] at h
      rw [Array.getD, dif_pos hk]
      exact Nat.lt_trans h (Nat.pow_lt_pow_right (by omega) (by omega))
    · rw [Array.getD, dif_neg hk]
      exact Nat.two_pow_pos _
  unfold encN
  rw [foldr_testBit X hrow (by omega), Array.getD_eq_getD_getElem?]
  simp [List.mem_range, hi]

@[expose] def MinorCheckF (F : Nat) (qs Bs : List Nat) : Prop :=
  ∀ a c : Fin 26, (∑ b : Fin 26,
    ((if F.testBit (128 * (minorRow a).val + (minorCol qs b).val) then (1 : ZMod 2) else 0) -
      (1 : Matrix (Fin 112) (Fin 112) (ZMod 2)) (minorRow a) (minorCol qs b)) *
    minorInv Bs b c) = if a = c then (1 : ZMod 2) else 0

instance (F : Nat) (qs Bs : List Nat) : Decidable (MinorCheckF F qs Bs) := by
  unfold MinorCheckF
  infer_instance

theorem minorCheck_iff {X : Array Nat} (hX : WfN X) (qs Bs : List Nat) :
    MinorCheck X qs Bs ↔ MinorCheckF (encN X) qs Bs := by
  unfold MinorCheck MinorCheckF
  have e : ∀ (a : Fin 26) (b : Fin 26),
      (CFSG.Sporadic.SmallF2.rowsMatrix 112 X - 1) (minorRow a) (minorCol qs b) =
        (if (encN X).testBit (128 * (minorRow a).val + (minorCol qs b).val) then (1 : ZMod 2)
          else 0) - (1 : Matrix (Fin 112) (Fin 112) (ZMod 2)) (minorRow a) (minorCol qs b) := by
    intro a b
    rw [Matrix.sub_apply, encN_testBit hX (minorRow a).isLt (minorCol qs b).isLt]
    rfl
  simp only [e]

theorem minor1_ok : MinorCheckF (prodFK c rm one (ef 1)) minorQ1 minorB1 := by
  decide +kernel

theorem minor14_ok : MinorCheckF (prodFK c rm one (ef 14)) minorQ14 minorB14 := by
  decide +kernel

open Certificates in
open CFSG.RankThree.PartOne CFSG.Sporadic.J4Schreier in
theorem c10058 :
    (MinorCheck (etaP 1).1 minorQ1 minorB1)
    ∧ (MinorCheck (etaP 14).1 minorQ14 minorB14) := by
  have h1 := etaP_ok 1
  have h14 := etaP_ok 14
  refine ⟨(minorCheck_iff h1.1.1 _ _).2 ?_, (minorCheck_iff h14.1.1 _ _).2 ?_⟩
  · rw [h1.1.2]
    exact minor1_ok
  · rw [h14.1.2]
    exact minor14_ok

end CertificateChecks.KernelJ4F2

end
