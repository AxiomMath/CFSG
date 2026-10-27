module

public import Certificates.Kernel.Sporadic.RawGen

public section

namespace CertificateChecks.KernelG24.Tri27206

@[expose] def triText : String :=
  include_str "../../../CFSG/LocalAnalysis/EvenSporadicStandard/Induction/Rows/G24TriTbl.txt"

@[expose] def laText : String :=
  include_str "../../../CFSG/LocalAnalysis/EvenSporadicStandard/Induction/Rows/G24LATbl.txt"

end CertificateChecks.KernelG24.Tri27206

set_option maxRecDepth 400000 in
#ks_chars CertificateChecks.KernelG24.Tri27206.TT CertificateChecks.KernelG24.Tri27206.triText

set_option maxRecDepth 400000 in
#ks_chars CertificateChecks.KernelG24.Tri27206.LT CertificateChecks.KernelG24.Tri27206.laText

end
