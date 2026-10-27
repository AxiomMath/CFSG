module

public import Certificates.Kernel.Misc.Perm.GH23LatData
public import Certificates.Kernel.Co1B.GenTri2045
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxRecDepth 400000

#kc_repo #kc_ktree CertificateChecks.KernelMisc.GH23Lat W3
  "Certificates/Kernel/Misc/Perm/GH23Lat/data/w3.bin" 64 4 806400 3376534097781396682

namespace CertificateChecks.KernelMisc.GH23Lat

@[expose] noncomputable def cv3 (s : Nat) : Bool := covS W3 15 s

end CertificateChecks.KernelMisc.GH23Lat

#kc_slices CertificateChecks.KernelMisc.GH23Lat.CV3 CertificateChecks.KernelMisc.GH23Lat.cv3 50

end
