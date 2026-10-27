module

public import Certificates.Kernel.LocalQT.HS4089.SD
public import Certificates.Kernel.SporSch.Ru.RowsGen
public import Certificates.Data.Kernel.LocalQT.BaseT
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicHSInputs
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
public import CFSG.Sporadic.HS
public import CFSG.Sporadic.Th.F2Spec
public import Certificates.Certificate113

set_option maxRecDepth 100000

public section

namespace CFSG.KD.LQT.H4089S

@[expose] noncomputable def famN (c : Nat) : Bool :=
  CFSG.KC.LQT.BT.nodesT 1100 11 CFSG.QuasithinUnique.K1.SporadicPerm.hsProg TF (Nat.mul c 8) 8

theorem valid : CFSG.QuasithinUnique.K1.SporadicPerm.slpValidAux
    CFSG.QuasithinUnique.K1.SporadicPerm.hsProg 2 = true := by
  decide +kernel

end CFSG.KD.LQT.H4089S

#kss_each CFSG.KD.LQT.H4089S.N CFSG.KD.LQT.H4089S.famN 28

end
