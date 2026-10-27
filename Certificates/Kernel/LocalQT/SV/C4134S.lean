module

public import Certificates.Kernel.LocalQT.Tc.Gen
public import Certificates.Data.Kernel.LocalQT.SylV
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1HeData
meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1HeCheckInputs
import CFSG.Assembly.LowTwoRankDefs
meta import CFSG.Foundations
meta import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
meta import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
meta import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
meta import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
meta import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
meta import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1HeSylArr
meta import CFSG.LocalAnalysis.SectionRank.SQT
meta import CFSG.Sporadic.HeldB.InnerCheck

set_option maxRecDepth 400000

namespace CFSG.KD.LQT.C4134

open CFSG.QuasithinUnique.Setup.X1

meta def sgM : List (Array Nat × Array Nat) := heSylGens

meta def parM : List Nat := parseNats heSylParStr

meta def labM : List Nat := parseNats heSylLabStr

meta def tabM : List Nat := parseNats heSylTabStr

end CFSG.KD.LQT.C4134

public section

#ks_chars CFSG.KD.LQT.C4134.CP CFSG.QuasithinUnique.Setup.X1.heSylParStr
#ks_chars CFSG.KD.LQT.C4134.CL CFSG.QuasithinUnique.Setup.X1.heSylLabStr
#ks_chars CFSG.KD.LQT.C4134.CT CFSG.QuasithinUnique.Setup.X1.heSylTabStr

#kqb_syl CFSG.KD.LQT.C4134.SY 8330 14 2048 CFSG.KD.LQT.C4134.sgM CFSG.KD.LQT.C4134.parM
  CFSG.KD.LQT.C4134.labM CFSG.KD.LQT.C4134.tabM

namespace CFSG.KD.LQT.C4134

open CFSG.KC.LQT.SV

@[expose] noncomputable def ckSY (s : Nat) : Bool :=
  chunkSV 8330 14 2048 4 SY.G SY.E SY.PT SY.LT SY.TB (Nat.mul s 4) 4

end CFSG.KD.LQT.C4134

end
