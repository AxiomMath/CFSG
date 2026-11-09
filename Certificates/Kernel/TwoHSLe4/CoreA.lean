module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFxPGCore
public import Certificates.Kernel.TwoHSLe4.SO5Eq

public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option synthInstance.maxSize 4096

namespace CertificateChecks.KernelTwoHSLe4.SO5

open CFSG.EvenSporadicStandard.TwoHS

@[expose] noncomputable def s0WP : List ℕ :=
  [23, 74, 24, 0, 71, 0, 45, 48, 24, 49, 74, 71, 73, 72, 98, 45, 98, 95, 96, 99, 5, 102, 103, 104,
    100, 26, 28, 81, 29, 27, 78, 108, 107, 105, 109, 58, 1, 2, 55, 3, 31, 54, 30, 32, 34, 83, 81, 80,
    82, 84, 43, 42, 51, 52, 50, 78, 76, 39, 77, 36, 118, 59, 56, 55, 57, 5, 110, 6, 8, 114, 61, 62,
    3, 2, 64, 10, 32, 34, 13, 14, 86, 88, 29, 87, 89, 66, 68, 109, 65, 69, 101, 100, 90, 94, 92, 43,
    12, 41, 42, 13, 113, 114, 111, 110, 92, 86, 16, 88, 89, 19, 38, 68, 35, 65, 39, 118, 119, 116,
    117, 64]

@[expose] noncomputable def s0WG : List ℕ :=
  [3, 5, 3, 0, 5, 0, 3, 3, 5, 3, 3, 3, 3, 3, 5, 5, 3, 3, 3, 3, 5, 3, 3, 3, 3, 3, 3, 5, 3, 3, 5, 3, 3,
    3, 3, 5, 3, 3, 5, 3, 3, 5, 3, 3, 3, 3, 3, 3, 3, 3, 5, 5, 3, 3, 3, 3, 3, 5, 3, 5, 5, 3, 3, 3, 3, 3,
    5, 3, 3, 5, 3, 3, 5, 5, 3, 3, 5, 5, 3, 3, 3, 3, 5, 3, 3, 3, 3, 5, 3, 3, 5, 5, 3, 3, 3, 3, 5, 3, 3,
    5, 3, 3, 3, 3, 5, 5, 3, 5, 5, 3, 3, 5, 3, 5, 3, 3, 3, 3, 3, 5]

@[expose] noncomputable def s0WD : List ℕ :=
  [8, 5, 5, 0, 9, 0, 9, 8, 5, 7, 5, 9, 7, 2, 7, 9, 7, 7, 9, 4, 1, 9, 8, 7, 4, 8, 7, 4, 6, 5, 4, 6, 4,
    9, 6, 9, 6, 6, 5, 1, 7, 8, 5, 5, 7, 8, 4, 9, 7, 6, 6, 6, 7, 8, 7, 4, 6, 2, 8, 7, 8, 8, 7, 5, 3, 1,
    7, 10, 6, 3, 9, 8, 1, 6, 4, 6, 5, 7, 3, 8, 8, 3, 6, 7, 5, 8, 7, 6, 2, 4, 4, 4, 5, 7, 6, 6, 8, 9,
    6, 3, 3, 3, 8, 7, 6, 8, 8, 3, 5, 5, 6, 7, 10, 2, 2, 8, 5, 6, 7, 4]

theorem s0W_ok : (List.range 120).all (fun i =>
    (s0WD.getD i 0 == 0 && (i == 5 || i == 3)) ||
    (Nat.blt (s0WD.getD (s0WP.getD i 0) 0) (s0WD.getD i 0) && Nat.blt (s0WP.getD i 0) 120 &&
      (s0WG.getD i 0 == 5 || s0WG.getD i 0 == 3) &&
      Nat.beq (S0 i) (mulK (S0 (s0WP.getD i 0)) (S0 (s0WG.getD i 0))))) = true := by
  decide +kernel

theorem s0_getD (i : ℕ) (hi : i < 120) : pgS0Code.getD i (unpk 0) = unpk (S0 i) := by
  rw [s0_eq, List.getD_eq_getElem?_getD]
  simp [S0L, hi]

theorem so5_S0_5 : IsSO5 (toM (unpk (S0 5))) := by
  rw [← s0_getD 5 (by norm_num)]
  have e : pgS0Code.getD 5 (unpk 0) = pgS1C := by decide +kernel
  rw [e]
  exact pgS1_so

theorem so5_S0_3 : IsSO5 (toM (unpk (S0 3))) := by
  rw [← s0_getD 3 (by norm_num)]
  decide +kernel

theorem so5_S0_all : ∀ i < 120, IsSO5 (toM (unpk (S0 i))) := by
  suffices h : ∀ n, ∀ i < 120, s0WD.getD i 0 = n → IsSO5 (toM (unpk (S0 i))) from
    fun i hi => h _ i hi rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro i hi hn
    have h := List.all_eq_true.1 s0W_ok i (List.mem_range.2 hi)
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, Nat.blt_eq] at h
    rcases h with ⟨-, h | h⟩ | ⟨⟨⟨hd, hp⟩, hg⟩, he⟩
    · rw [h]
      exact so5_S0_5
    · rw [h]
      exact so5_S0_3
    · have hg' : IsSO5 (toM (unpk (S0 (s0WG.getD i 0)))) := by
        rcases hg with hg | hg
        · rw [hg]
          exact so5_S0_5
        · rw [hg]
          exact so5_S0_3
      rw [Nat.eq_of_beq_eq_true he, ← fmMul_unpk]
      exact isSO5_fmMul (ih _ (hn ▸ hd) _ hp rfl) hg'

theorem c_s0 : pgS0Code.length = 120 ∧ pgS0Code.Nodup ∧ pgD0Code.length = 8 ∧ pgD0Code.Nodup := by
  have h1 : (pgS0Code.map fun a => a.toList.foldr (fun x c => Nat.add x (Nat.mul 8 c)) 0).Nodup := by
    decide +kernel
  have h2 : (pgD0Code.map fun a => a.toList.foldr (fun x c => Nat.add x (Nat.mul 8 c)) 0).Nodup := by
    decide +kernel
  refine ⟨by decide +kernel, h1.of_map _, by decide +kernel, h2.of_map _⟩

theorem c_ok : (∀ a ∈ pgS0Code, fmOk a) ∧ (∀ a ∈ pgD0Code, fmOk a) ∧
    fmOk pgR0C ∧ fmOk pgSf0C ∧ fmOk pgTau1C ∧ fmOk pgS1C := by
  decide +kernel

theorem c_so : (∀ a ∈ pgS0Code, IsSO5 (toM a)) ∧ ∀ a ∈ pgD0Code, IsSO5 (toM a) := by
  refine ⟨?_, ?_⟩
  · rw [s0_eq]
    intro a ha
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ha
    simp only [S0L, List.mem_map, List.mem_range] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    exact so5_S0_all i hi
  · intro a ha
    simp only [pgD0Code, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil,
      or_false] at ha
    obtain ⟨k, hk, rfl | rfl⟩ := ha
    · have h := pg_r_so (k : ZMod 4)
      rw [ZMod.val_natCast_of_lt hk] at h
      rw [pgRotC, toM_fmPow]
      exact h
    · have h := pg_sr_so (k : ZMod 4)
      rw [ZMod.val_natCast_of_lt hk] at h
      rw [pgReflC, toM_fmMul, toM_fmPow]
      exact h

theorem c_d0 : pgS1C ∈ pgS0Code ∧ fmMul pgS1C pgS1C = fmOne ∧
    (∀ x ∈ pgD0Code, fmMul x x = pgTau1C → x = pgR0C ∨ x = fmPow pgR0C 3) ∧
    (∀ x ∈ pgD0Code, fmMul x x = fmOne → x ≠ fmOne → x ≠ pgTau1C →
      x = pgReflC 0 ∨ x = pgReflC 1 ∨ x = pgReflC 2 ∨ x = pgReflC 3) ∧
    (∀ x ∈ pgD0Code, fmMul x x = fmOne → x ≠ fmOne → x ≠ pgTau1C → fmTr x ≠ fmTr pgTau1C) ∧
    pgR0C ∈ pgD0Code ∧ pgSf0C ∈ pgD0Code ∧ pgTau1C ∈ pgD0Code ∧
    fmMul pgR0C pgR0C = pgTau1C ∧ fmMul pgSf0C pgSf0C = fmOne ∧ fmMul pgSf0C pgR0C = pgReflC 1 ∧
    (∀ k ∈ ([0, 1, 2, 3] : List ℕ), fmMul (pgReflC k) (pgReflC k) = fmOne) ∧
    fmMul pgTau1C pgTau1C = fmOne ∧ fmMul pgTau1C pgS1C = fmMul pgS1C pgTau1C := by
  decide +kernel

end CertificateChecks.KernelTwoHSLe4.SO5

end
