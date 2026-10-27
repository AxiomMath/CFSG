module

public import Certificates.Kernel.Sporadic.HexNumsGen
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicFi24TwoBData
public import Certificates.Data.CFSGNative.Co3Schreier.Basic
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.Sporadic.Fi22.C2068
public import Certificates.Kernel.Sporadic.Fi22.C3151

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelLC.Fi24BT.Kd
  CFSG.ComponentClassification.RankTwoSporadic.Fi24Prime.fi24KdText
#ks_hexnums CertificateChecks.KernelLC.Fi24BT.Kd
  CFSG.ComponentClassification.RankTwoSporadic.Fi24Prime.fi24KdText 3 9
#ks_chars CertificateChecks.KernelLC.Fi24BT.Kdd
  CFSG.ComponentClassification.RankTwoSporadic.Fi24Prime.fi24KddText
#ks_hexnums CertificateChecks.KernelLC.Fi24BT.Kdd
  CFSG.ComponentClassification.RankTwoSporadic.Fi24Prime.fi24KddText 3 9
#ks_chars CertificateChecks.KernelLC.Fi24BT.Rep
  CFSG.ComponentClassification.RankTwoSporadic.Fi24Prime.fi24NRepText
#ks_hexnums CertificateChecks.KernelLC.Fi24BT.Rep
  CFSG.ComponentClassification.RankTwoSporadic.Fi24Prime.fi24NRepText 3 9
#ks_chars CertificateChecks.KernelLC.Fi24BT.T0
  CFSG.ComponentClassification.RankTwoSporadic.Fi24Prime.fi24NTreeText0
#ks_hexnums CertificateChecks.KernelLC.Fi24BT.T0
  CFSG.ComponentClassification.RankTwoSporadic.Fi24Prime.fi24NTreeText0 4 16
#ks_chars CertificateChecks.KernelLC.Fi24BT.T1
  CFSG.ComponentClassification.RankTwoSporadic.Fi24Prime.fi24NTreeText1
#ks_hexnums CertificateChecks.KernelLC.Fi24BT.T1
  CFSG.ComponentClassification.RankTwoSporadic.Fi24Prime.fi24NTreeText1 4 16
#ks_chars CertificateChecks.KernelLC.Fi24BT.T2
  CFSG.ComponentClassification.RankTwoSporadic.Fi24Prime.fi24NTreeText2
#ks_hexnums CertificateChecks.KernelLC.Fi24BT.T2
  CFSG.ComponentClassification.RankTwoSporadic.Fi24Prime.fi24NTreeText2 4 16

namespace CertificateChecks.KernelLC.Fi24BT

open CFSG.KS.Raw CFSG.KS.HexNums CFSG.Sporadic.FischerOddCore
open CFSG.ComponentClassification.RankTwoSporadic.Fi24Prime

theorem kd_eq : hexNums 3 fi24KdText = unpack 8064 9 Kd.F := hexNums_of Kd.eq Kd.ok
theorem kdd_eq : hexNums 3 fi24KddText = unpack 10584 9 Kdd.F := hexNums_of Kdd.eq Kdd.ok
theorem rep_eq : hexNums 3 fi24NRepText = unpack 1008 9 Rep.F := hexNums_of Rep.eq Rep.ok
theorem t0_eq : hexNums 4 fi24NTreeText0 = unpack 1700 16 T0.F := hexNums_of T0.eq T0.ok
theorem t1_eq : hexNums 4 fi24NTreeText1 = unpack 377 16 T1.F := hexNums_of T1.eq T1.ok
theorem t2_eq : hexNums 4 fi24NTreeText2 = unpack 2015 16 T2.F := hexNums_of T2.eq T2.ok

end CertificateChecks.KernelLC.Fi24BT

namespace CertificateChecks.KernelLC.Fi24BW

open CFSG.ComponentClassification.RankTwoSporadic.Fi24Prime CFSG.Sporadic.Schreier.Co3.Native

@[expose] def dD : List (List Int) := fi24KdWords.toList.drop 5
@[expose] def ddD : List (List Int) := fi24KddWords.toList.drop 10

theorem dW : fi24KdWords = wordsArr 5 16 dD := by decide +kernel
theorem ddW : fi24KddWords = wordsArr 10 21 ddD := by decide +kernel

end CertificateChecks.KernelLC.Fi24BW

end
