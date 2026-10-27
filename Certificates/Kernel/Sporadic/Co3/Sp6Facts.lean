module

public import Certificates.Kernel.Sporadic.Co3.Sp36
public import CFSG.Certificates.Kernel.Misc.PairCountSound
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Co3Sp6

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.PairCount
open CFSG.Sporadic.Schreier.Co3 CFSG.Sporadic.Schreier.Co3.Native
open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

theorem forms : ∀ a < 64,
    decide (a ∈ co3A) = decide ((Finset.univ.filter fun n : Fin 64 =>
      co3Sp6Form a (co3Vec6 n) = 0).card = 36) := by
  decide +kernel

theorem formsList : co3A.Nodup ∧ 0 ∈ co3A ∧ (∀ i < 6, 2 ^ i ∈ co3A) ∧ (∀ a ∈ co3A, a < 64) := by
  decide +kernel

theorem actionP : ∀ k < 63, ∀ r < 36, pg 6 (mask 6) (Co3Sp36.S k) r < 36 ∧
    co3A.getD (pg 6 (mask 6) (Co3Sp36.S k) r) 0 = co3A.getD r 0 ^^^
      (if co3Sp6Form (co3A.getD r 0) (co3Vec6 (k + 1)) = 0 then co3Sp6J (k + 1) else 0) := by
  decide +kernel

theorem action : ∀ k < 63, ∀ r < 36, (co3Sp36Arrs[k]!)[r]! < 36 ∧
    co3A.getD (co3Sp36Arrs[k]!)[r]! 0 = co3A.getD r 0 ^^^
      (if co3Sp6Form (co3A.getD r 0) (co3Vec6 (k + 1)) = 0 then co3Sp6J (k + 1) else 0) := by
  intro k hk r hr
  rw [Co3Sp36.arr_eq k (by omega), unpack_get hr]
  exact actionP k hk r hr

theorem moversP : ∀ c < 36, 1 ≤ c → ∃ j < 63, pg 6 (mask 6) (Co3Sp36.S j) 0 = 0 ∧
    pg 6 (mask 6) (Co3Sp36.S j) c ≠ c := by
  decide +kernel

theorem movers : ∀ c < 36, 1 ≤ c → ∃ j < 63, (co3Sp36Arrs[j]!)[0]! = 0 ∧ (co3Sp36Arrs[j]!)[c]! ≠ c := by
  intro c hc h1
  obtain ⟨j, hj, h⟩ := moversP c hc h1
  refine ⟨j, hj, ?_⟩
  rw [Co3Sp36.arr_eq j (by omega), unpack_get (by norm_num), unpack_get hc]
  exact h

theorem orbits : rawOrbitSizes 36 co3Sp36Arrs co3Sp36BaseArr = [36, 35, 18, 8, 4, 2] := by
  rw [rawOrbitSizesK_sound Co3Sp36.binds Co3Sp36.perm Co3Sp36.hl]
  decide

theorem pts_size_zero_of {n : Nat} {S : Array (Array Nat)} {base : Array Nat} {k : Nat}
    {l : List Nat} (h : rawOrbitSizes n S base = k :: l) :
    ((rawLevels n S base)[0]!).pts.size = k := by
  unfold rawOrbitSizes at h
  generalize rawLevels n S base = A at h ⊢
  rcases A with ⟨_ | ⟨x, xs⟩⟩
  · simp at h
  · simp only [List.map_cons, List.cons.injEq] at h
    rw [getElem!_pos _ 0 (by simp)]
    simpa using h.1

theorem pts0 : ((rawLevels 36 co3Sp36Arrs co3Sp36BaseArr)[0]!).pts.size = 36 :=
  pts_size_zero_of orbits

theorem facts : (∀ a < 64,
      decide (a ∈ co3A) = decide ((Finset.univ.filter fun n : Fin 64 =>
        co3Sp6Form a (co3Vec6 n) = 0).card = 36)
    )
    ∧ (co3A.Nodup ∧ 0 ∈ co3A ∧ (∀ i < 6, 2 ^ i ∈ co3A) ∧ (∀ a ∈ co3A, a < 64))
    ∧ (∀ k < 63, ∀ r < 36, (co3Sp36Arrs[k]!)[r]! < 36 ∧
      co3A.getD (co3Sp36Arrs[k]!)[r]! 0 = co3A.getD r 0 ^^^
        (if co3Sp6Form (co3A.getD r 0) (co3Vec6 (k + 1)) = 0 then co3Sp6J (k + 1) else 0)
    )
    ∧ (rawChainOK 36 (co3Sp36Arrs.extract 0 co3Sp36GenCount) co3Sp36Arrs co3Sp36BaseArr
        (wordsArr co3Sp36GenCount co3Sp36StrongCount co3Sp36Derivations) 4 = true ∧
      rawOrbitSizes 36 co3Sp36Arrs co3Sp36BaseArr = [36, 35, 18, 8, 4, 2] ∧
      ((rawLevels 36 co3Sp36Arrs co3Sp36BaseArr)[0]!).pts.size = 36 ∧
      (∀ c < 36, 1 ≤ c → ∃ j < 63, (co3Sp36Arrs[j]!)[0]! = 0 ∧ (co3Sp36Arrs[j]!)[c]! ≠ c)
    ) :=
  ⟨forms, formsList, action,
    rawChainK_sound (NS := 1) (CH := 36) Co3Sp36.binds Co3Sp36.head Co3Sp36.hl (by norm_num)
      Co3Sp36.hs, orbits, pts0, movers⟩

end CertificateChecks.KernelSpor.Co3Sp6

end
