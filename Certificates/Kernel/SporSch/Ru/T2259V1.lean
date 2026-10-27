module

public import Certificates.Kernel.SporSch.Ru.T2259K
public import Certificates.Kernel.SporSch.Ru.RowsGen
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.Ru2259

@[expose] noncomputable def v1 (i : Nat) : Bool := blk (Nat.add 29 i)

end CertificateChecks.KernelSporSch.Ru2259

#kss_each CertificateChecks.KernelSporSch.Ru2259.V1 CertificateChecks.KernelSporSch.Ru2259.v1 29

end
