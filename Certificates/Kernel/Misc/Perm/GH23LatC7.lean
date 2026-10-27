module

public import Certificates.Kernel.Misc.Perm.GH23LatData
public import Certificates.Kernel.Co1B.GenTri2045
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxRecDepth 400000

#kc_repo #kc_ktree CertificateChecks.KernelMisc.GH23Lat W7
  "Certificates/Kernel/Misc/Perm/GH23Lat/data/w7.bin" 64 4 806400 16873563615716524138

namespace CertificateChecks.KernelMisc.GH23Lat

@[expose] noncomputable def cv7 (s : Nat) : Bool := covS W7 35 s

end CertificateChecks.KernelMisc.GH23Lat

#kc_slices CertificateChecks.KernelMisc.GH23Lat.CV7 CertificateChecks.KernelMisc.GH23Lat.cv7 50

end
