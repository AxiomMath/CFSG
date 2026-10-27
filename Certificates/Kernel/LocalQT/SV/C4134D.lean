module

public import Certificates.Kernel.LocalQT.Tc.Gen
public import Certificates.Data.Kernel.LocalQT.SlpP
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

namespace CFSG.KD.LQT.C4134

open CFSG.QuasithinUnique.Setup.X1

meta def gM : List (Array Nat × Array Nat) := [heA0P, heA1P]

meta def gRM : List (Array Nat × Array Nat) := [heA0P, heA1P, heUP]

meta def t0M : List (Array Nat × Array Nat) := [heT0P]

meta def t1M : List (Array Nat × Array Nat) := [heT1ArrP]

meta def tuM : List (Array Nat × Array Nat) := [heUP]

end CFSG.KD.LQT.C4134

public section

#kqb_mc CFSG.KD.LQT.C4134.T0 8330 14 CFSG.KD.LQT.C4134.gM CFSG.KD.LQT.C4134.t0M
  CFSG.QuasithinUnique.Setup.X1.heT0Words CFSG.QuasithinUnique.Setup.X1.heT0Prog
#kqb_mc CFSG.KD.LQT.C4134.T1 8330 14 CFSG.KD.LQT.C4134.gM CFSG.KD.LQT.C4134.t1M
  CFSG.QuasithinUnique.Setup.X1.heT1Words CFSG.QuasithinUnique.Setup.X1.heT1Prog
#kqb_mc CFSG.KD.LQT.C4134.TU 8330 14 CFSG.KD.LQT.C4134.gM CFSG.KD.LQT.C4134.tuM
  CFSG.QuasithinUnique.Setup.X1.heUWords CFSG.QuasithinUnique.Setup.X1.heUProg
#kqb_run CFSG.KD.LQT.C4134.RS 8330 14 CFSG.KD.LQT.C4134.gRM
  CFSG.QuasithinUnique.Setup.X1.heSylProg

namespace CFSG.KD.LQT.C4134

open CFSG.QuasithinUnique.Setup.X1 CFSG.KC.LQT.SP

@[expose] noncomputable def D0 : List (Int × Int) := nodesOf (layMC 2 1 heT0Words heT0Prog)

@[expose] noncomputable def D1 : List (Int × Int) := nodesOf (layMC 2 1 heT1Words heT1Prog)

@[expose] noncomputable def DU : List (Int × Int) := nodesOf (layMC 2 1 heUWords heUProg)

@[expose] noncomputable def DR : List (Int × Int) := nodesOf (layRun 3 heSylProg)

@[expose] noncomputable def ckT0 (s : Nat) : Bool :=
  nodesSP 8330 14 3 D0 T0.X T0.XI (Nat.add 3 (Nat.mul s 8)) 8

@[expose] noncomputable def ckT1 (s : Nat) : Bool :=
  nodesSP 8330 14 3 D1 T1.X T1.XI (Nat.add 3 (Nat.mul s 8)) 8

@[expose] noncomputable def ckTU (s : Nat) : Bool :=
  nodesSP 8330 14 3 DU TU.X TU.XI (Nat.add 3 (Nat.mul s 8)) 8

@[expose] noncomputable def ckRS (s : Nat) : Bool :=
  nodesSP 8330 14 3 DR RS.X RS.XI (Nat.add 3 (Nat.mul s 8)) 8

end CFSG.KD.LQT.C4134

end
