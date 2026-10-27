module

public import Certificates.Kernel.SporSch.Mathieu.M12MData
public import Certificates.Data.Kernel.SporSch.OddConj
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicM12EndTests
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicM12Data
public import CFSG.Certificates.Kernel.LocalCompUnpack
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.GeneralizedFitting
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicGenCensus
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicM12EndData
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicPairCensus
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.Monster.Code.Weights

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.M12Over

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KS.SporSch.MOC CertificateChecks.KernelSporSch
open CFSG.ComponentClassification.RankTwoSporadic.M12

@[expose] def T0 : Nat := 561278236226537825205121694215504966

@[expose] def wsP : List (Nat × Nat) :=
  [(766540054383559003218293450970796193, 722557702043941648306727732994480137),
   (940396119103676927705540288084746533, 819721686001333253555568327002335339),
   (778182117604263232168807504737996103, 934143719718938457183076845834284264),
   (892373712961333552491865358143270116, 816145642271602614180877352084579594),
   (902793528311499896550751450074123591, 932973714117604425412839883332981898),
   (858572843457434271236913659410383050, 521450071954879627476927673143602402),
   (858737483176836029421420229145395399, 605824856375323666330669980299961602),
   (566469338429492512510075154380988704, 558687193251829195806913242606964896)]

@[expose] def eb : List Bool := [true, false, true, true, false, false, true, true, true, false]

theorem bval_eb : bval eb = 1485 := by decide

theorem kT0 : bindArrK (m12T0 m12E0) 24 5 T0 = true := by quickRfl

@[expose] noncomputable def witOK (c ci : Nat) : Bool :=
  permOK 24 5 (mask 5) (24 * 5) c ci && canonK 24 5 (mask 5) (24 * 5) c &&
    siftK 24 5 (mask 5) (24 * 5) (pidn 24 5) M12DQ.LR M12DQ.TRI M12DQ.BP 5 0 c &&
    Nat.beq (pcomp 24 5 (mask 5) c T0) (pcomp 24 5 (mask 5) T0 c)

theorem kWit : allPairsK witOK wsP = true := by quickRfl

theorem kCnt : rcnt (M12DQ.LR 0) = 12 ∧ rcnt (M12DQ.LR 1) = 11 := by decide +kernel

@[expose] noncomputable def cK (k₀ k₁ : Nat) : Bool :=
  Nat.beq (cntOddBad2K 24 5 (mask 5) (24 * 5) (pidn 24 5) M12DQ.LR M12DQ.TR 5 eb wsP k₀ k₁) 0

end CertificateChecks.KernelLC.M12Over

end
