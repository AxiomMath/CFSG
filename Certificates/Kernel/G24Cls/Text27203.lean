module

public import Certificates.Kernel.Sporadic.RawGen

public section

namespace CertificateChecks.KernelG24.Cls27203

@[expose] def clsText : String :=
  include_str "../../../CFSG/LocalAnalysis/EvenSporadicStandard/Induction/Rows/G24ClassTbl.txt"

end CertificateChecks.KernelG24.Cls27203

set_option maxRecDepth 400000 in
#ks_chars CertificateChecks.KernelG24.Cls27203.CT CertificateChecks.KernelG24.Cls27203.clsText

end
