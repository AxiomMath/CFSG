module

public import Certificates.Kernel.Sporadic.RawTreeGen
public import Certificates.Kernel.SchreierFam.He725W
public meta import Certificates.Data.Insp443He
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSchreierFam.He725

meta def baseX : Array Nat := #[0, 1, 2, 3, 4]

end CertificateChecks.KernelSchreierFam.He725

#ks_rawtree CertificateChecks.KernelSchreierFam.He725X 8330 14 64 64 0
  CFSG.SectionRank.QTK.Insp443.He.l7S CertificateChecks.KernelSchreierFam.He725.baseX 2
  CertificateChecks.KernelSchreierFam.He725.dL

end
