module

public import CFSG.Certificates.Kernel.LocalQTSylSound
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M12CheckInputs
public import CFSG.Sporadic.Schreier.MathieuOddCoreM12Outer
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Foundations
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.LocalAnalysis.SectionRank.Sporadic.LocalWitness

set_option maxRecDepth 100000

public section

namespace CFSG.KD.LQT.C4069

open CFSG.KC.LQT.Syl CFSG.KC.LQT.W CFSG.QuasithinUnique.Setup.X1 CFSG.Sporadic.Schreier

@[expose] def h1 : List (Nat × Nat) :=
    [(0, 0), (1, 0), (2, 0), (0, 14), (0, 33), (2, 1), (3, 0), (0, 3), (1, 1), (3, 2), (4, 0), (0,
    4), (0, 9), (0, 2), (5, 0), (1, 2), (2, 6), (5, 1), (5, 4), (4, 1), (2, 5), (6, 0), (4, 2), (0,
    11), (4, 5), (5, 5), (1, 8)]

theorem hA : codeP ((CFSG.Sporadic.Mathieu.m12a : _) : Equiv.Perm (Fin 12)) =
    184726996899603491 := by decide +kernel
theorem hB : codeP ((CFSG.Sporadic.Mathieu.m12b : _) : Equiv.Perm (Fin 12)) =
    365002956609719367 := by decide +kernel

noncomputable abbrev RL : List Nat :=
  rlK 12 184726996899603491 365002956609719367 m12RGens m12RWords

theorem kS : sylK 12 6 RL = true := by quickRfl
theorem kR : rankK 12 (invK 12 RL) 4 = true := by quickRfl
theorem k1 : g1okK 12 184726996899603491 365002956609719367 RL m12G1 11 = true := by quickRfl
theorem k1c : g1covK 12 RL m12G1 h1 = true := by quickRfl

theorem kO : (m12Sigma * (evalCodes [m12A1, m12B1] m12OuterWord * m12Sigma *
      (evalCodes [m12A1, m12B1] m12OuterWord)⁻¹)) ^ 11 = 1 ∧
    m12Sigma * (evalCodes [m12A1, m12B1] m12OuterWord * m12Sigma *
      (evalCodes [m12A1, m12B1] m12OuterWord)⁻¹) ≠ 1 := by decide +kernel

end CFSG.KD.LQT.C4069

end
