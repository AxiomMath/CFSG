module

public import Certificates.Kernel.J27031.M
public import Certificates.Data.Kernel.LocalQT.BaseT
public import Certificates.Kernel.Sporadic.J2K.Data
public import Certificates.Data.Kernel.Spor.PEnum
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicJ2Inputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Foundations
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.QuasithinUnique.K1.Interface
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicRep
public import CFSG.Sporadic.Bridge.J2
public import CFSG.Sporadic.J2.Simple
public import CFSG.Sporadic.Th.F2Spec
public import Certificates.Certificate113
public import Certificates.Data.Kernel.DcKN

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

public section

namespace CFSG.KD.J27031.NA

open CFSG.KC.LQT.BT CFSG.QuasithinUnique.K1.SporadicPerm CertificateChecks.KernelSpor.J2K

theorem nodes : (List.range 25).all (fun c => nodesT 315 14 j2Prog S.TF (c * 8) 8) = true := by
  quickRfl

theorem ab_ok : (List.range 315).all (fun x => im (S.TF 0) x == CFSG.KS.PEnum.r32 AL x &&
    im (S.TF 1) x == CFSG.KS.PEnum.r32 BE x) = true := by
  quickRfl

@[expose] noncomputable def invPairs : List (Nat × Nat) :=
  [(abc 0, P.TF 0), (abc 1, P.TF 1), (rtc 0, P.TF 2), (rtc 1, P.TF 3), (rtc 2, P.TF 4)]

theorem inv_ok : invPairs.all (fun c => (List.range 315).all fun p =>
    im c.2 (im c.1 p) == p && im c.1 (im c.2 p) == p && decide (im c.1 p < 315) &&
      decide (im c.2 p < 315)) = true := by
  quickRfl

end CFSG.KD.J27031.NA

end
