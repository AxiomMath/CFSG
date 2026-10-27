module

public import Certificates.Kernel.Misc.Perm.GH23LatData
public import Certificates.Kernel.Co1B.GenTri2045
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxRecDepth 400000

#kc_repo #kc_ktree CertificateChecks.KernelMisc.GH23Lat W6
  "Certificates/Kernel/Misc/Perm/GH23Lat/data/w6.bin" 64 4 806400 15384493514854868976

namespace CertificateChecks.KernelMisc.GH23Lat

@[expose] noncomputable def cv6 (s : Nat) : Bool := covS W6 30 s

end CertificateChecks.KernelMisc.GH23Lat

#kc_slices CertificateChecks.KernelMisc.GH23Lat.CV6 CertificateChecks.KernelMisc.GH23Lat.cv6 50

end
