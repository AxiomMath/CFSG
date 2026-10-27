module

public import Certificates.Kernel.LocalQT.Tc.Gen
public import Certificates.Data.Kernel.LocalQT.J2Idx
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42J2CheckInputs
meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42J2CheckInputs
public import CFSG.Foundations
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.Sporadic.SmallOddCore.J2Data
meta import CFSG.Foundations
meta import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
meta import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
meta import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
meta import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
meta import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
meta import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
meta import CFSG.LocalAnalysis.SectionRank.SQT
meta import CFSG.Sporadic.SmallOddCore.J2Data

namespace CFSG.KD.LQT.C4127

open CFSG.QuasithinUnique.Bridge.J2Excl

meta def sgM : List (Array Nat × Array Nat) := j2SylGens

meta def parM : List Nat := j2Par

meta def labM : List Nat := j2Lab

meta def tabM : List Nat := j2Tab

meta def repsM : List (Nat × Nat) := j2Reps

end CFSG.KD.LQT.C4127

public section

set_option maxRecDepth 400000

#ks_chars CFSG.KD.LQT.C4127.CP CFSG.QuasithinUnique.Bridge.J2Excl.j2SylParStr
#ks_chars CFSG.KD.LQT.C4127.CL CFSG.QuasithinUnique.Bridge.J2Excl.j2SylLabStr
#ks_chars CFSG.KD.LQT.C4127.CT CFSG.QuasithinUnique.Bridge.J2Excl.j2SylTabStr

#kqb_syl CFSG.KD.LQT.C4127.SY 315 9 256 CFSG.KD.LQT.C4127.sgM CFSG.KD.LQT.C4127.parM
  CFSG.KD.LQT.C4127.labM CFSG.KD.LQT.C4127.tabM

#kqb_idx CFSG.KD.LQT.C4127.IX 256 8 8 12 CFSG.KD.LQT.C4127.tabM CFSG.KD.LQT.C4127.parM
  CFSG.KD.LQT.C4127.labM CFSG.KD.LQT.C4127.repsM

namespace CFSG.KD.LQT.C4127

open CFSG.KC.LQT.SV CFSG.KC.LQT.JX CFSG.QuasithinUnique.Bridge.J2Excl

@[expose] noncomputable def ckSY (s : Nat) : Bool :=
  chunkSV 315 9 256 8 SY.G SY.E SY.PT SY.LT SY.TB (Nat.mul s 32) 32

@[expose] noncomputable def ckRow (s : Nat) : Bool :=
  rowsJX 8 12 256 8 SY.PT SY.LT SY.TB IX.MR IX.IT IX.GW j2Reps (Nat.mul s 32) 32

@[expose] noncomputable def ckTri (s : Nat) : Bool :=
  trisJX 8 12 256 IX.MR IX.GW (Nat.mul s 32) 32

end CFSG.KD.LQT.C4127

end
