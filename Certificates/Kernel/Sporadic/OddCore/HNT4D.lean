module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Kernel.SporSch.Th.GenV4
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicHNData
meta import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicHNTests
meta import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicHNData
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Assembly.Defs

namespace CertificateChecks.KernelSpor.HNT4O

open CFSG.ComponentClassification.RankTwoSporadic.HN

meta def poolN : List Nat := (parseNatsHN hnT4PoolStr).toList
meta def witN : List Nat := (parseNatsHN hnT4WitStr).toList

meta def starts (a : Array Nat) (len : Nat → Nat) : List Nat := Id.run do
  let mut out : Array Nat := #[]
  let mut i := 0
  for _ in [0:a.size] do
    if i < a.size then
      out := out.push i
      i := i + len i
  return (out.push i).toList

meta def poolP : List Nat :=
  let a := parseNatsHN hnT4PoolStr
  starts a fun i => 2 + a[i]! + a[i + 1 + a[i]!]!

meta def witP : List Nat :=
  let a := parseNatsHN hnT4WitStr
  starts a fun i =>
    if a[i]! = 0 then 1 else if a[i]! = 1 then 3 + a[i + 1]! else if a[i]! = 2 then 3 else 2

meta def cP : Array (Array Nat) := (poolT4 (decodePoolT4 hnT4PoolStr)).map (·.1)
meta def cQ : Array (Array Nat) := (poolT4 (decodePoolT4 hnT4PoolStr)).map (·.2)

end CertificateChecks.KernelSpor.HNT4O

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSpor.HNT4T.Pool
  CFSG.ComponentClassification.RankTwoSporadic.HN.hnT4PoolStr
#ks_chars CertificateChecks.KernelSpor.HNT4T.Wit
  CFSG.ComponentClassification.RankTwoSporadic.HN.hnT4WitStr
#kss_natlist CertificateChecks.KernelSpor.HNT4T.QN CertificateChecks.KernelSpor.HNT4O.poolN
#kss_natlist CertificateChecks.KernelSpor.HNT4T.WN CertificateChecks.KernelSpor.HNT4O.witN
#kss_natlist CertificateChecks.KernelSpor.HNT4T.QP CertificateChecks.KernelSpor.HNT4O.poolP
#kss_natlist CertificateChecks.KernelSpor.HNT4T.WP CertificateChecks.KernelSpor.HNT4O.witP

#kmisc_packarrs CertificateChecks.KernelSpor.HNT4C.P CertificateChecks.KernelSpor.HNT4O.cP 10
#kmisc_packarrs CertificateChecks.KernelSpor.HNT4C.Q CertificateChecks.KernelSpor.HNT4O.cQ 10

end
