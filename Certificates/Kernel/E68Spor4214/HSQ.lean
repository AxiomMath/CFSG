module

public import Certificates.Data.E68Spor.Words
public import Certificates.Data.CFSGNative.SporLat.Spec
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

public section

namespace CFSG.KD.E68S4214

open CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Quasithin.E6.Spor

@[expose] def hsUT : Array (Array Nat) :=
  (hsUWords.map (wordTabA #[hsTa, hsTb] 1100)).toArray

@[expose] def qp0 : List (Nat × Nat) := [(0, 0)]

end CFSG.KD.E68S4214

end
