module

public import Certificates.Kernel.MonsterExist.Eb.Sound
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 100000

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CertificateChecks.MonsterExist.Eb

open CFSG.KC CFSG.KC.Loop CFSG.Monster CFSG.Monster.B CFSG.Monster.Existence
  CFSG.Monster.B.TwoA.Census CertificateChecks.MonsterExist.ShortKey

theorem case1_0 : case1Range 0 512 = true := by quickRfl
theorem case1_1 : case1Range 512 512 = true := by quickRfl
theorem case1_2 : case1Range 1024 512 = true := by quickRfl
theorem case1_3 : case1Range 1536 512 = true := by quickRfl
theorem case1_4 : case1Range 2048 512 = true := by quickRfl
theorem case1_5 : case1Range 2560 512 = true := by quickRfl
theorem case1_6 : case1Range 3072 512 = true := by quickRfl
theorem case1_7 : case1Range 3584 512 = true := by quickRfl

theorem case1_all : ∀ a < 4096, case1Bucket a = true := by
  intro a ha
  have h : ∀ c < 8, case1Range (512 * c) 512 = true := by
    intro c hc
    interval_cases c
    exacts [case1_0, case1_1, case1_2, case1_3, case1_4, case1_5, case1_6, case1_7]
  have := (case1Range_iff _ _).1 (h (a / 512) (by omega)) (a % 512) (Nat.mod_lt _ (by norm_num))
  rwa [Nat.div_add_mod] at this

theorem tree_ok : treeOK = true := by quickRfl

theorem edge_0 : edgeRange 0 64 = true := by quickRfl
theorem edge_1 : edgeRange 64 64 = true := by quickRfl
theorem edge_2 : edgeRange 128 64 = true := by quickRfl
theorem edge_3 : edgeRange 192 64 = true := by quickRfl

theorem edge_all : ∀ i < 256, ∀ k < 24, edgeAt i k = true := by
  intro i hi
  have h : ∀ c < 4, edgeRange (64 * c) 64 = true := by
    intro c hc
    interval_cases c
    exacts [edge_0, edge_1, edge_2, edge_3]
  have := (edgeRange_iff _ _).1 (h (i / 64) (by omega)) (i % 64) (Nat.mod_lt _ (by norm_num))
  rwa [Nat.div_add_mod] at this

theorem bound_ok : boundOK = true := by quickRfl

theorem sh1_ok : ∀ j < 120, absentL 26 256 CL (spt j) = false ∧ memK (spt j % 2 ^ 24) = true := by
  decide +kernel

theorem sh2_ok : ∀ i < 256, memK (pt i % 2 ^ 24) = true → absentL 26 120 SH (pt i) = false := by
  decide +kernel

theorem main_0 : ∀ j < 30, ∀ j' < 120, absentL 26 120 SH (mulEnc (spt (30 * 0 + j)) (spt j')) = true := by
  decide +kernel
theorem main_1 : ∀ j < 30, ∀ j' < 120, absentL 26 120 SH (mulEnc (spt (30 * 1 + j)) (spt j')) = true := by
  decide +kernel
theorem main_2 : ∀ j < 30, ∀ j' < 120, absentL 26 120 SH (mulEnc (spt (30 * 2 + j)) (spt j')) = true := by
  decide +kernel
theorem main_3 : ∀ j < 30, ∀ j' < 120, absentL 26 120 SH (mulEnc (spt (30 * 3 + j)) (spt j')) = true := by
  decide +kernel

theorem main_all : ∀ j < 120, ∀ j' < 120, absentL 26 120 SH (mulEnc (spt j) (spt j')) = true := by
  intro j hj
  have h : ∀ c < 4, ∀ j < 30, ∀ j' < 120,
      absentL 26 120 SH (mulEnc (spt (30 * c + j)) (spt j')) = true := by
    intro c hc
    interval_cases c
    exacts [main_0, main_1, main_2, main_3]
  have := h (j / 30) (by omega) (j % 30) (Nat.mod_lt _ (by norm_num))
  rwa [Nat.div_add_mod] at this

theorem case1OK_true : case1OK = true :=
  case1OK_of_buckets case1_all

theorem class0OK_true :
    class0OK = true :=
  class0OK_of_checks tree_ok edge_all bound_ok sh1_ok sh2_ok main_all

theorem witness_memK : memK 245763 = true ∧ memK 245820 = false ∧ memK 196611 = false ∧
    memK 734 = false := by
  decide +kernel

theorem witness_shortness :
    isShortX (packP (false, 3, 60)) = true ∧ isShortX (packP (false, 60, 60)) = false ∧
      isShortX (packP (false, 3, 48)) = false ∧ isShortX (packP (false, 734, 0)) = false := by
  have e1 : packP (false, 3, 60) = 245763 := rfl
  have e2 : packP (false, 60, 60) = 245820 := rfl
  have e3 : packP (false, 3, 48) = 196611 := rfl
  have e4 : packP (false, 734, 0) = 734 := rfl
  rw [e1, e2, e3, e4, ← memK_eq_isShortX (by norm_num), ← memK_eq_isShortX (by norm_num),
    ← memK_eq_isShortX (by norm_num), ← memK_eq_isShortX (by norm_num)]
  exact witness_memK

end CertificateChecks.MonsterExist.Eb

end
