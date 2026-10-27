module

public import Certificates.Kernel.SporSch.Co1.AutK
public import Certificates.Kernel.SporSch.Co1.Stab2148
public import CFSG.Certificates.Kernel.SporSch.Co1TowerSound
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

namespace CertificateChecks.KernelSporSch.Co1Aut

open CFSG.KC.Enum CFSG.KS.Raw CFSG.KS.SporSch.M24 CFSG.KS.SporSch.VOrb
open CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.SmallF2.Native
open CertificateChecks.KernelSporSch.Co1Stab CertificateChecks.KernelSporSch.Co1Packed
open CertificateChecks.KernelSporSch.Co1Orbs CertificateChecks.KernelSporSch.Co1Stab2148

theorem dag_eq : stabDag = ((List.range SD.N).map fun i => unpack 24 24 (SD.M i),
    (List.range SD.N).map fun i => unpack 24 24 (SD.MI i), true) := by
  unfold stabDag
  refine dagIK_sound ?_ kD
  rw [h0u, h1u, ← Nat.eq_of_beq_eq_true kb0, ← Nat.eq_of_beq_eq_true kb1]
  rfl

theorem cols_eq : stabColsT =
    Array.ofFn (n := 85) fun j => transposeRows 24 (unpack 24 24 (SD.M j.val)) := by
  unfold stabColsT
  rw [dag_eq, Nat.eq_of_beq_eq_true kN]
  refine congrArg (Array.ofFn (n := 85)) (funext fun j => congrArg (transposeRows 24) ?_)
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range j.2, Option.map_some,
    Option.getD_some]

theorem tower : stabTowerCheck = true := by
  unfold stabTowerCheck
  rw [cols_eq, tower_sound (M := SD.M) (K := 85) ?_ ?_, dag_eq, Nat.eq_of_beq_eq_true kN]
  · simp
  · intro i hi
    have : i < 5 := by simpa [Data.stabTowerBase] using hi
    interval_cases i <;> decide
  · intro i hi
    have : i < 5 := by simpa [Data.stabTowerBase] using hi
    interval_cases i
    · exact ⟨_, _, _, _, _, 512, TW.hd0, TW.hc0, TW.hn0, by decide, TW.hl0, TW.hp0, f0⟩
    · exact ⟨_, _, _, _, _, 512, TW.hd1, TW.hc1, TW.hn1, by decide, TW.hl1, TW.hp1, f1⟩
    · exact ⟨_, _, _, _, _, 512, TW.hd2, TW.hc2, TW.hn2, by decide, TW.hl2, TW.hp2, f2⟩
    · exact ⟨_, _, _, _, _, 512, TW.hd3, TW.hc3, TW.hn3, by decide, TW.hl3, TW.hp3, f3⟩
    · exact ⟨_, _, _, _, _, 512, TW.hd4, TW.hc4, TW.hn4, by decide, TW.hl4, TW.hp4, f4⟩

theorem nonlin : nonlinCheck = true := by
  have h : nonlinCheck = nonlinP aR (stabVec 0) (stabVec 3) 11752856 15263478 Data.nonlinVecs
      (stabOrb 3) (fullOrb 2) := by
    unfold nonlinCheck nonlinCheckOf tauOf nonlinP
    rfl
  rw [h, aR_u, full2]
  refine nonlinK_sound (fun u => ?_) (fun u => qF u) kNL
  rw [so]
  exact q3 4600 rfl u

end CertificateChecks.KernelSporSch.Co1Aut

end
