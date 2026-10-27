module

public import Certificates.Kernel.LocalQT.Base.C4143D
public import Certificates.Kernel.SporSch.Ru.RowsGen
public import Certificates.Data.Kernel.LocalQT.BaseT
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicRuInputs
public import CFSG.Foundations
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.QuasithinUnique.K1.Interface
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicBaseVec
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicRep
public import CFSG.Sporadic.Ru
public import CFSG.Sporadic.Th.F2Spec
public import Certificates.Certificate113

set_option maxRecDepth 100000

public section

namespace CFSG.KD.LQT.C4143

@[expose] noncomputable def famN (c : Nat) : Bool :=
  CFSG.KC.LQT.BT.nodesT 4060 12 CFSG.QuasithinUnique.K1.SporadicPerm.ruProg TF (Nat.mul c 8) 8

end CFSG.KD.LQT.C4143

#kss_each CFSG.KD.LQT.C4143.N CFSG.KD.LQT.C4143.famN 26

end
