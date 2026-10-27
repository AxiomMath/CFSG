module

public import Certificates.Kernel.He7149.D
public import Certificates.Kernel.LocalQT.Base.C4141D
public import Certificates.Data.Kernel.E64F
public import Certificates.Data.Kernel.LocalQT.PermW
public import CFSG.Quasithin.Vol2.KGFactE64HeData
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicHeInputs
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
public import CFSG.Sporadic.He
public import CFSG.Sporadic.Th.F2Spec
public import Certificates.Certificate113

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

public section

namespace CFSG.KD.He7149

open CFSG.KC.E64F CFSG.Quasithin.H13.KGE64 CFSG.QuasithinUnique.Ch1.SporLat.He
open CFSG.QuasithinUnique.K1.SporadicPerm

@[expose] noncomputable def LF (l p : Nat) : Nat := CFSG.KC.LQT.PW.imgW 14 (TF l) p

@[expose] noncomputable def LAB (l p : Nat) : Nat := CFSG.KC.LQT.PW.imgW 14 (CFSG.KD.LQT.C4141.TF l) p

@[expose] def w7 : List Nat := (heMwLit[7]!).headD []

theorem lt_ok : (Nat.beq (TF 0) (CFSG.KD.LQT.C4141.TF 197) && Nat.beq (TF 1) (CFSG.KD.LQT.C4141.TF 207) &&
    Nat.beq (TF 2) (CFSG.KD.LQT.C4141.TF 226) && Nat.beq (TF 3) (CFSG.KD.LQT.C4141.TF 247)) = true := by
  quickRfl

theorem w4_ok : (List.range 8330).all (fun p => Nat.beq (LF 4 p) (wordF LAB w7 p)) = true := by
  quickRfl

theorem e64_ok : e64CheckF heB LF 5 heE64Y heE64O heLabels7 = true := by
  quickRfl

end CFSG.KD.He7149

end
