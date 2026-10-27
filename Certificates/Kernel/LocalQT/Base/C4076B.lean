module

public import Certificates.Kernel.LocalQT.Base.C4076D
public import Certificates.Kernel.LocalQT.Base.C4143D
public import Certificates.Kernel.LocalQT.Base.C4143E
public import Certificates.Kernel.SporSch.Ru.RowsGen
public import Certificates.Data.Kernel.LocalQT.FusionS
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

namespace CFSG.KD.LQT.C4076

@[expose] noncomputable def famB (c : Nat) : Bool :=
  CFSG.KC.LQT.FS.bfsS 12 CFSG.QuasithinUnique.K1.SporadicPerm.ruB
    CFSG.QuasithinUnique.K1.SporadicPerm.ruQp C4143.TF 64 C4143.RT 16384 14 15 C4143.E BO IB PT CT
    (Nat.mul c 1024) 1024

end CFSG.KD.LQT.C4076

#kss_each CFSG.KD.LQT.C4076.B CFSG.KD.LQT.C4076.famB 16

end
