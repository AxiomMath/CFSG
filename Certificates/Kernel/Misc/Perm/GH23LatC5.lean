module

public import Certificates.Kernel.Misc.Perm.GH23LatData
public import Certificates.Kernel.Co1B.GenTri2045
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxRecDepth 400000

#kc_repo #kc_ktree CertificateChecks.KernelMisc.GH23Lat W5
  "Certificates/Kernel/Misc/Perm/GH23Lat/data/w5.bin" 64 4 806400 10367824475686295447

namespace CertificateChecks.KernelMisc.GH23Lat

@[expose] noncomputable def cv5 (s : Nat) : Bool := covS W5 25 s

end CertificateChecks.KernelMisc.GH23Lat

#kc_slices CertificateChecks.KernelMisc.GH23Lat.CV5 CertificateChecks.KernelMisc.GH23Lat.cv5 50

end
