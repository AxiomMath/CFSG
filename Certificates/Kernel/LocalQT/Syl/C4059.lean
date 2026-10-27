module

public import CFSG.Certificates.Kernel.LocalQTSyl24Sound
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M24CheckInputs
public import Certificates.Kernel.LocalQT.Syl.D4059
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.LocalQTSylSound
public import CFSG.Foundations
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1AutModel
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1OuterGen
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.LocalAnalysis.SectionRank.Sporadic.LocalWitness
public import CFSG.Sporadic.Schreier.M24
public import CFSG.Sporadic.Schreier.MathieuOddCoreWords

set_option maxRecDepth 100000

public section

namespace CFSG.KD.LQT.C4059

open CFSG.KC.LQT.Syl CFSG.KC.LQT.W CFSG.QuasithinUnique.Setup.X1

theorem hA : codeP ((CFSG.Sporadic.Mathieu.m24a : _) : Equiv.Perm (Fin 24)) =
    817395973838868159142633316802379971 := by decide +kernel
theorem hB : codeP ((CFSG.Sporadic.Mathieu.m24b : _) : Equiv.Perm (Fin 24)) =
    938078705133617800621527216201835139 := by decide +kernel

noncomputable abbrev RL : List Nat :=
  rlK 24 817395973838868159142633316802379971 938078705133617800621527216201835139 m24RGens
    m24RWords

noncomputable abbrev PL : List Nat :=
  List.map (evalZK 24 [817395973838868159142633316802379971, 938078705133617800621527216201835139])
    m24PoolWords

theorem kS : sylG2K 24 10 RL (List.map (evalZK 24 [817395973838868159142633316802379971,
    938078705133617800621527216201835139]) m24RGens) = true := by quickRfl
theorem kP : lenIs (pairK 24 (invK 24 RL)) 12546 = true := by quickRfl
theorem k1 : g1okPK 24 PL RL m24G1 11 = true := by quickRfl
theorem k1c : g1covK 24 RL m24G1 h1 = true := by quickRfl
theorem k11 : g2okPK 24 PL RL m24G2_11 11 = true := by quickRfl
theorem k11c : atMost (badK 24 RL m24G2_11 (unpackK 12546 c11)) 0 = true := by quickRfl
theorem k23 : g2okPK 24 PL RL m24G2_23 23 = true := by quickRfl
theorem k23c : atMost (badK 24 RL m24G2_23 (unpackK 12546 c23)) 888 = true := by quickRfl

end CFSG.KD.LQT.C4059

end
