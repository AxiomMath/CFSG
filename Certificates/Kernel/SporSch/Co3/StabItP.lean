module

public import Certificates.Kernel.SporSch.Co3.StabIt
public import CFSG.Certificates.Kernel.Spor.SiftRSound
public import CFSG.Certificates.Kernel.Spor.RawAgree
public import CFSG.Certificates.Kernel.Spor.TextSound
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.Certificates.Kernel.Spor.RawOrbGrp

public section

namespace CertificateChecks.KernelSporSch.Co3SIC

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Sporadic.Schreier.Co3 CFSG.Sporadic.Schreier.Co3.Native
open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CertificateChecks.KernelSpor

theorem arr_eq (j : Nat) (hj : j < 8) : co3StabItArrs[j]! = unpack 276 9 (S j) := by
  have hL := CFSG.KS.Text.hexBind_sound Co3SI.all j (by change j < 8; omega)
  rw [Nat.zero_add, ← Co3SI.eq, ← Nat.eq_of_beq_eq_true (allN_spec lines j hj)] at hL
  rw [co3StabItArrs, getElem!_pos _ j (by simp; omega), Array.getElem_ofFn]
  exact hL

theorem binds : Binds 276 9 S 8 7 BP co3StabItArrs co3StabItBaseArr :=
  ⟨by norm_num, by norm_num, by norm_num, by simp [co3StabItArrs], arr_eq, by decide, by decide⟩

theorem facts : rawChainOK 276 (co3StabItArrs.extract 0 8) co3StabItArrs co3StabItBaseArr
      (wordsArr 8 8 co3StabItDerivations) 4 = true ∧
    rawOrbitSizes 276 co3StabItArrs co3StabItBaseArr = [276, 275, 162, 105, 64, 3, 2] ∧
    (∀ j < 8, siftA 276 co3ChainLevels co3ChainBaseArr 0 co3StabItArrs[j]! = true) ∧
    (∀ k < 3, (co3StabItLevels[5]!).pts[k]! ∈ co3ItNat → k = 0) := by
  refine ⟨rawChainK_sound (NS := 18) (CH := 16) binds head hl (by norm_num) hs,
    by rw [rawOrbitSizesK_sound binds perm hl]; decide, fun j hj => ?_, fun k hk hm => ?_⟩
  · obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 (allN_spec sift j hj)
    exact siftK_soundR Co3C.binds Co3C.perm Co3C.hl (arr_eq j hj) (Nat.eq_of_beq_eq_true h2)
      (range_of_permOK (allN_spec perm j hj)) h1
  · obtain ⟨A, -⟩ := CFSG.KS.Raw.Orb.agree_levelK binds perm (fun t ht => by
      rw [binds.2.2.2.2.2.2 t ht]; interval_cases t <;> decide) (i := 5) (by norm_num) (hl 5 (by norm_num))
    have hlev :
        CFSG.Certificates.ChainArrays.lev 276 co3StabItArrs co3StabItBaseArr 5 = co3StabItLevels[5]! :=
      rfl
    have hsz : (co3StabItLevels[5]!).pts.size = 3 := by
      rw [← hlev, ← A.cnt]
      decide
    have hpt : ∀ k < 3, (co3StabItLevels[5]!).pts[k]! = rpt 9 (mask 9) (LR 5) k := fun k hk =>
      (A.pt k (by rw [hlev, hsz]; exact hk)).symm
    rw [hpt k hk] at hm
    interval_cases k
    · rfl
    · rw [Nat.eq_of_beq_eq_true lev5a] at hm
      exact absurd hm (by decide)
    · rw [Nat.eq_of_beq_eq_true lev5b] at hm
      exact absurd hm (by decide)

end CertificateChecks.KernelSporSch.Co3SIC

end
