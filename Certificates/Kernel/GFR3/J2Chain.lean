module

public import CFSG.HardMathSupport.Solomon.Coordinator.GFR3J2Inputs
public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Misc.Perm.HexCmd
public meta import CFSG.HardMathSupport.Solomon.Coordinator.GFR3J2Inputs
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR3Core
public meta import CFSG.HardMathSupport.Solomon.Coordinator.GFR3Core
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Core
public meta import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Core
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public meta import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public meta import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public meta import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public meta import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public meta import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public meta import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.GLTheoremB.QuotientTools
public meta import CFSG.LocalAnalysis.GLTheoremB.QuotientTools

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelGFR3.J2

open CFSG.HardMathSupport.Solomon.Coordinator

@[expose] def d : List (List ℤ) := j2ThreeWords.toList.drop 2

end CertificateChecks.KernelGFR3.J2

end

#ks_chars CertificateChecks.KernelGFR3.J2.JS CFSG.Sporadic.Schreier.PairNative.j2StrongHex
#kmisc_hexflat CertificateChecks.KernelGFR3.J2.JS CFSG.Sporadic.Schreier.PairNative.j2StrongHex
  4 315 9 2
#ks_chars CertificateChecks.KernelGFR3.J2.JH CFSG.HardMathSupport.Solomon.Coordinator.j2ThreeHex
#kmisc_hexflat CertificateChecks.KernelGFR3.J2.JH
  CFSG.HardMathSupport.Solomon.Coordinator.j2ThreeHex 3 315 9 7
#ks_rawchain CertificateChecks.KernelGFR3.J2.C 315 9 63
  CFSG.HardMathSupport.Solomon.Coordinator.j2ThreeArrs
  CFSG.HardMathSupport.Solomon.Coordinator.j2ThreeBaseArr 2 CertificateChecks.KernelGFR3.J2.d
