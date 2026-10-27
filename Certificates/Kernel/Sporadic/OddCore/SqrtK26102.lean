module

public import Certificates.Kernel.Sporadic.OddCore.J2CnK
public import Certificates.Kernel.Sporadic.OddCore.J3Cent
public import Certificates.Kernel.SporSch.PairJ3.Chain
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Data.Kernel.Spor.Prim
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC3HCheck
meta import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC3HCheck
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Rows
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic
public import CFSG.Walter.JRFacts
meta import CFSG.GroupTheory.Fitting.CharacteristicP
meta import CFSG.GroupTheory.LocalCores.Components
meta import CFSG.GroupTheory.LocalCores.Fitting
meta import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
meta import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
meta import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
meta import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
meta import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
meta import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
meta import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Rows
meta import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
meta import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
meta import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic
meta import CFSG.Walter.JRFacts

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSpor.TC3HJ2T CFSG.EvenSporadicStandard.Fin76b.TC3H.j2Hex

#kmisc_hexflat CertificateChecks.KernelSpor.TC3HJ2T CFSG.EvenSporadicStandard.Fin76b.TC3H.j2Hex
  3 315 9 3

#ks_chars CertificateChecks.KernelSpor.TC3HJ3T CFSG.EvenSporadicStandard.Fin76b.TC3H.j3Hex

#kmisc_hexflat CertificateChecks.KernelSpor.TC3HJ3T CFSG.EvenSporadicStandard.Fin76b.TC3H.j3Hex
  4 513 13 24

namespace CertificateChecks.KernelSpor.SqrtK26102

open CFSG.EvenSporadicStandard.Fin76b.TC3H CFSG.Sporadic.SmallOddCore.Native

meta def j3TcM : Array (Array Nat) := (List.range 2).toArray.map fun k => natArr (j3Tbl k)

end CertificateChecks.KernelSpor.SqrtK26102

#kmisc_packarrs CertificateChecks.KernelSpor.TC3HJ3P CertificateChecks.KernelSpor.SqrtK26102.j3TcM 13

namespace CertificateChecks.KernelSpor.SqrtK26102

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.Join
open CertificateChecks.KernelSporSch

theorem tc3h_join : joinK 12 (13 * 513) TC3HJ3T.F TC3HJ3P 2 = true := by
  quickRfl

@[expose] noncomputable def sqK (n w u a y : Nat) (s : Bool) : Bool :=
  bAnd(szOK n w, bAnd(canonK n w (mask w) (n * w) u, bAnd(canonK n w (mask w) (n * w) a,
  bAnd(canonK n w (mask w) (n * w) y,
  bAnd(invEqK n w (mask w) (n * w) y (pcomp n w (mask w) y (pcomp n w (mask w) y y)),
  bAnd(s, Nat.beq (pcomp n w (mask w) y y) a))))))

@[expose] def yuWord : List Int := [4, 2, 3, 1, 2, 3, 1, 2, 3, 1, 3, 3, 3, 5, 1, 4]

@[expose] noncomputable def j3W (wd : List Int) (p : Nat) : Bool :=
  wordEqK 6156 13 (mask 13) (pidn 6156 13) PJ3.S PJ3.SI 5 wd p

theorem k26102_a : sqK 315 9 (J2Cn.F 0) (J2Cn.F 31) (TC3HJ2T.F 1)
    (J2Cn.sK (TC3HJ2T.F 1) || J2Cn.sK (pcomp 315 9 (mask 9) (TC3HJ2T.F 1) (J2Cn.F 0))) = true := by
  quickRfl

theorem k26102_b : sqK 315 9 (J2Cn.F 0) (J2Cn.F 17) (TC3HJ2T.F 2)
    (J2Cn.sK (TC3HJ2T.F 2) || J2Cn.sK (pcomp 315 9 (mask 9) (TC3HJ2T.F 2) (J2Cn.F 0))) = true := by
  quickRfl

theorem k26103 : sqK 6156 13 (J3CentP 0) (J3CentP 9) (TC3HJ3P 1)
    (j3W yuWord (pcomp 6156 13 (mask 13) (TC3HJ3P 1) (J3CentP 0))) = true := by
  quickRfl

theorem k26102_neg : sqK 315 9 (J2Cn.F 0) (J2Cn.F 31)
    (pcomp 315 9 (mask 9) (TC3HJ2T.F 1) (TC3HJ2T.F 1)) true = false := by
  decide +kernel

theorem k26103_neg : sqK 6156 13 (J3CentP 0) (J3CentP 9)
    (pcomp 6156 13 (mask 13) (TC3HJ3P 1) (TC3HJ3P 1)) true = false := by
  decide +kernel

theorem k26103_word_neg : j3W yuWord (TC3HJ3P 1) = false := by
  decide +kernel

end CertificateChecks.KernelSpor.SqrtK26102

end
