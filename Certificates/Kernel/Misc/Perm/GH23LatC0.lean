module

public import Certificates.Kernel.Misc.Perm.GH23LatData
public import Certificates.Kernel.Co1B.GenTri2045
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxRecDepth 400000

#kc_repo #kc_ktree CertificateChecks.KernelMisc.GH23Lat W0
  "Certificates/Kernel/Misc/Perm/GH23Lat/data/w0.bin" 64 4 806400 6788750291660703506

namespace CertificateChecks.KernelMisc.GH23Lat

@[expose] noncomputable def cv0 (s : Nat) : Bool := covS W0 0 s

end CertificateChecks.KernelMisc.GH23Lat

#kc_slices CertificateChecks.KernelMisc.GH23Lat.CV0 CertificateChecks.KernelMisc.GH23Lat.cv0 50

end
