module

public import Certificates.Kernel.SporSch.Mathieu.Gen
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentHeInnerData
public meta import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentHeInnerData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLQT.He4148

open CFSG.KS.SporSch.MOCG CFSG.QuasithinUnique.Id2519.HeInner

meta def SX : Array (Array Nat) := strongOf 105 heSigmaP.toArray heXpWords

meta def baseX : Array Nat := #[1, 0, 2, 3]

meta def SD : Array (Array Nat) := strongOf 105 heDpGens.toArray heDpWords

meta def baseD : Array Nat := #[1, 0, 2]

end CertificateChecks.KernelLQT.He4148

#ks_rawchain CertificateChecks.KernelLQT.He4148.XQ 105 7 16 CertificateChecks.KernelLQT.He4148.SX
  CertificateChecks.KernelLQT.He4148.baseX 9 CFSG.QuasithinUnique.Id2519.HeInner.heXpWords

#ks_rawchain CertificateChecks.KernelLQT.He4148.DQ 105 7 16 CertificateChecks.KernelLQT.He4148.SD
  CertificateChecks.KernelLQT.He4148.baseD 5 CFSG.QuasithinUnique.Id2519.HeInner.heDpWords

end
