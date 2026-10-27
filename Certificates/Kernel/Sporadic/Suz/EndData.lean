module

public import Certificates.Kernel.SporSch.GenPerms
public import Certificates.Kernel.Sporadic.RawGenSplit
public import CFSG.Certificates.Kernel.Misc.HexFlatSound
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicSuzEndTests
import Certificates.Kernel.Misc.Perm.HexCmd
meta import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicSuzEndTests
public meta import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicSuzData
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.GeneralizedFitting
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicGenCensus
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicPairCensus
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.Monster.Code.Weights
meta import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
meta import CFSG.LocalAnalysis.ComponentClassification.GeneralizedFitting
meta import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
meta import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
meta import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
meta import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicGenCensus
meta import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicPairCensus
meta import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
meta import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
meta import CFSG.Monster.Code.Weights

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSpor.SuzEndE
  CFSG.ComponentClassification.RankTwoSporadic.Suz.suzE0Text

#kmisc_hexflat CertificateChecks.KernelSpor.SuzEndE
  CFSG.ComponentClassification.RankTwoSporadic.Suz.suzE0Text 3 1782 11 2

namespace CertificateChecks.KernelSpor.SuzEnd

open CFSG.ComponentClassification.RankTwoSporadic.Suz CFSG.Monster.B.Co2.Native

@[expose] def noDerivs : List (List Int) := []

@[expose] def suzEndHWords : List (List Nat) :=
  [[0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 0],
   [0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0]]

@[expose] def suzEndSWords : List (List Nat) :=
  [[0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1],
   [0, 1, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1],
   [0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 0, 1, 1, 1, 0, 0, 1, 0],
   [0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1]]

meta def hWordsM : List (List Nat) :=
  [[0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 0],
   [0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0]]

meta def sWordsM : List (List Nat) :=
  [[0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1],
   [0, 1, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1],
   [0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 0, 1, 1, 1, 0, 0, 1, 0],
   [0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1]]

meta def invM (t : Array Nat) : Array Nat := invCand 1782 t

meta def commM (x y : Array Nat) : Array Nat :=
  compA 1782 (compA 1782 (compA 1782 x y) (invM x)) (invM y)

meta def wordL (w : List Nat) : Array Nat :=
  w.foldl (fun acc i => compA 1782 suzEndL[i]! acc) (idA 1782)

meta def eiM : Array (Array Nat) := suzE0.map invM

meta def bM : Array Nat := suzEndB0

meta def biM : Array Nat := invM suzEndB0

meta def xM : Array (Array Nat) := suzEndLeaves

meta def xiM : Array (Array Nat) := suzEndLeaves.map invM

meta def yM : Array (Array Nat) :=
  let l := (Array.range 4).map fun i => commM suzEndLeaves[2 * i]! suzEndLeaves[2 * i + 1]!
  l ++ #[commM l[0]! l[1]!, commM l[2]! l[3]!]

meta def yiM : Array (Array Nat) := yM.map invM

meta def sgM : Array (Array Nat) := #[suzEndSigma, suzEndC0]

meta def sgiM : Array (Array Nat) := sgM.map invM

meta def lM : Array (Array Nat) := suzEndL ++ (hWordsM.map wordL).toArray

meta def baseL : Array Nat := #[0, 1]

meta def sM : Array (Array Nat) := (sWordsM.map wordL).toArray

meta def baseS : Array Nat := #[0]

end CertificateChecks.KernelSpor.SuzEnd

#kss_perms CertificateChecks.KernelSpor.SuzEnd.EI 11 CertificateChecks.KernelSpor.SuzEnd.eiM
#ks_perm CertificateChecks.KernelSpor.SuzEnd.B 11 CertificateChecks.KernelSpor.SuzEnd.bM
#ks_perm CertificateChecks.KernelSpor.SuzEnd.BI 11 CertificateChecks.KernelSpor.SuzEnd.biM
#kss_perms CertificateChecks.KernelSpor.SuzEnd.X 11 CertificateChecks.KernelSpor.SuzEnd.xM
#kss_perms CertificateChecks.KernelSpor.SuzEnd.XI 11 CertificateChecks.KernelSpor.SuzEnd.xiM
#kss_perms CertificateChecks.KernelSpor.SuzEnd.Y 11 CertificateChecks.KernelSpor.SuzEnd.yM
#kss_perms CertificateChecks.KernelSpor.SuzEnd.YI 11 CertificateChecks.KernelSpor.SuzEnd.yiM
#kss_perms CertificateChecks.KernelSpor.SuzEnd.SG 11 CertificateChecks.KernelSpor.SuzEnd.sgM
#kss_perms CertificateChecks.KernelSpor.SuzEnd.SGI 11 CertificateChecks.KernelSpor.SuzEnd.sgiM

#ks_rawchain_sl2_data CertificateChecks.KernelSpor.SuzEL 1782 11 16 64
  CertificateChecks.KernelSpor.SuzEnd.lM CertificateChecks.KernelSpor.SuzEnd.baseL 4
  CertificateChecks.KernelSpor.SuzEnd.noDerivs

#ks_rawchain_sl2_data CertificateChecks.KernelSpor.SuzES 1782 11 4 64
  CertificateChecks.KernelSpor.SuzEnd.sM CertificateChecks.KernelSpor.SuzEnd.baseS 4
  CertificateChecks.KernelSpor.SuzEnd.noDerivs

end
