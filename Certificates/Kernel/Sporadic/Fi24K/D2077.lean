module

public import Certificates.Kernel.Sporadic.HexNumsGen
public import CFSG.Sporadic.FischerOddCore.Fi24R2KCheckInputs
public import Certificates.Data.CFSGNative.Co3Schreier.Basic
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSpor.Fi24T.K CFSG.Sporadic.FischerOddCore.fi24KText
#ks_hexnums CertificateChecks.KernelSpor.Fi24T.K CFSG.Sporadic.FischerOddCore.fi24KText 3 9
#ks_chars CertificateChecks.KernelSpor.Fi24T.P CFSG.Sporadic.FischerOddCore.fi24PText
#ks_hexnums CertificateChecks.KernelSpor.Fi24T.P CFSG.Sporadic.FischerOddCore.fi24PText 3 9
#ks_chars CertificateChecks.KernelSpor.Fi24T.S0 CFSG.Sporadic.FischerOddCore.fi24S0Text
#ks_hexnums CertificateChecks.KernelSpor.Fi24T.S0 CFSG.Sporadic.FischerOddCore.fi24S0Text 3 9
#ks_chars CertificateChecks.KernelSpor.Fi24T.Tree CFSG.Sporadic.FischerOddCore.fi24STreeText
#ks_hexnums CertificateChecks.KernelSpor.Fi24T.Tree CFSG.Sporadic.FischerOddCore.fi24STreeText 3 10

namespace CertificateChecks.KernelSpor.Fi24T

open CFSG.KS.Raw CFSG.KS.HexNums CFSG.Sporadic.FischerOddCore

theorem k_eq : hexNums 3 fi24KText = unpack 6048 9 K.F := hexNums_of K.eq K.ok
theorem p_eq : hexNums 3 fi24PText = unpack 3780 9 P.F := hexNums_of P.eq P.ok
theorem s0_eq : fi24S0 = unpack 504 9 S0.F := hexNums_of S0.eq S0.ok
theorem tree_eq : fi24STree = unpack 377 10 Tree.F := hexNums_of Tree.eq Tree.ok

end CertificateChecks.KernelSpor.Fi24T

namespace CertificateChecks.KernelSpor.Fi24W

open CFSG.Sporadic.FischerOddCore CFSG.Sporadic.Schreier.Co3.Native

@[expose] def kD : List (List Int) := fi24KWords.toList.drop 2
@[expose] def pD : List (List Int) := fi24PWords.toList.drop 2

theorem kW : fi24KWords = wordsArr 2 12 kD := by decide +kernel
theorem pW : fi24PWords = wordsArr 2 10 pD := by decide +kernel

end CertificateChecks.KernelSpor.Fi24W

end
