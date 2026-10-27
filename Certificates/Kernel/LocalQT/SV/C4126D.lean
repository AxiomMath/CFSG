module

public import Certificates.Kernel.LocalQT.Tc.Gen
public import Certificates.Data.Kernel.LocalQT.SlpP
public import Certificates.Data.Kernel.LocalQT.SylV
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42HSData
meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42HSCheckInputs
import CFSG.Assembly.LowTwoRankDefs
meta import CFSG.Foundations
meta import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
meta import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
meta import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
meta import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
meta import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
meta import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42HSData
meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1HeSylArr
meta import CFSG.LocalAnalysis.SectionRank.SQT

namespace CFSG.KD.LQT.C4126

open CFSG.QuasithinUnique.Bridge.HSExcl CFSG.QuasithinUnique.Setup.X1

meta def gM : List (Array Nat × Array Nat) := [hsA0P, hsA1P]

meta def t0M : List (Array Nat × Array Nat) := [hsTP 5]

meta def t1M : List (Array Nat × Array Nat) := [hsTP 12]

meta def t2M : List (Array Nat × Array Nat) := [hsTP 21]

meta def t3M : List (Array Nat × Array Nat) := [hsTP 34]

meta def sgM : List (Array Nat × Array Nat) := hsSylGens

meta def parM : List Nat := parseNats hsSylParStr

meta def labM : List Nat := parseNats hsSylLabStr

meta def tabM : List Nat := parseNats hsSylTabStr

end CFSG.KD.LQT.C4126

public section

set_option maxRecDepth 400000

#kqb_mc CFSG.KD.LQT.C4126.T0 3850 12 CFSG.KD.LQT.C4126.gM CFSG.KD.LQT.C4126.t0M
  CFSG.QuasithinUnique.Bridge.HSExcl.hsT0Words CFSG.QuasithinUnique.Bridge.HSExcl.hsT0Prog
#kqb_mc CFSG.KD.LQT.C4126.T1 3850 12 CFSG.KD.LQT.C4126.gM CFSG.KD.LQT.C4126.t1M
  CFSG.QuasithinUnique.Bridge.HSExcl.hsT1Words CFSG.QuasithinUnique.Bridge.HSExcl.hsT1Prog
#kqb_mc CFSG.KD.LQT.C4126.T2 3850 12 CFSG.KD.LQT.C4126.gM CFSG.KD.LQT.C4126.t2M
  CFSG.QuasithinUnique.Bridge.HSExcl.hsT2Words CFSG.QuasithinUnique.Bridge.HSExcl.hsT2Prog
#kqb_mc CFSG.KD.LQT.C4126.T3 3850 12 CFSG.KD.LQT.C4126.gM CFSG.KD.LQT.C4126.t3M
  CFSG.QuasithinUnique.Bridge.HSExcl.hsT3Words CFSG.QuasithinUnique.Bridge.HSExcl.hsT3Prog

#ks_chars CFSG.KD.LQT.C4126.CP CFSG.QuasithinUnique.Bridge.HSExcl.hsSylParStr
#ks_chars CFSG.KD.LQT.C4126.CL CFSG.QuasithinUnique.Bridge.HSExcl.hsSylLabStr
#ks_chars CFSG.KD.LQT.C4126.CT CFSG.QuasithinUnique.Bridge.HSExcl.hsSylTabStr

#kqb_syl CFSG.KD.LQT.C4126.SY 3850 12 1024 CFSG.KD.LQT.C4126.sgM CFSG.KD.LQT.C4126.parM
  CFSG.KD.LQT.C4126.labM CFSG.KD.LQT.C4126.tabM

namespace CFSG.KD.LQT.C4126

open CFSG.QuasithinUnique.Bridge.HSExcl CFSG.KC.LQT.SP CFSG.KC.LQT.SV

@[expose] noncomputable def D0 : List (Int × Int) := nodesOf (layMC 2 1 hsT0Words hsT0Prog)

@[expose] noncomputable def D1 : List (Int × Int) := nodesOf (layMC 2 1 hsT1Words hsT1Prog)

@[expose] noncomputable def D2 : List (Int × Int) := nodesOf (layMC 2 1 hsT2Words hsT2Prog)

@[expose] noncomputable def D3 : List (Int × Int) := nodesOf (layMC 2 1 hsT3Words hsT3Prog)

@[expose] noncomputable def ckT0 (s : Nat) : Bool :=
  nodesSP 3850 12 3 D0 T0.X T0.XI (Nat.add 3 (Nat.mul s 16)) 16

@[expose] noncomputable def ckT1 (s : Nat) : Bool :=
  nodesSP 3850 12 3 D1 T1.X T1.XI (Nat.add 3 (Nat.mul s 16)) 16

@[expose] noncomputable def ckT2 (s : Nat) : Bool :=
  nodesSP 3850 12 3 D2 T2.X T2.XI (Nat.add 3 (Nat.mul s 16)) 16

@[expose] noncomputable def ckT3 (s : Nat) : Bool :=
  nodesSP 3850 12 3 D3 T3.X T3.XI (Nat.add 3 (Nat.mul s 16)) 16

@[expose] noncomputable def ckSY (s : Nat) : Bool :=
  chunkSV 3850 12 1024 4 SY.G SY.E SY.PT SY.LT SY.TB (Nat.mul s 8) 8

end CFSG.KD.LQT.C4126

end
