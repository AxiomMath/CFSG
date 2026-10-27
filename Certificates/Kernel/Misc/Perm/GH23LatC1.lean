module

public import Certificates.Kernel.Misc.Perm.GH23LatData
public import Certificates.Kernel.Co1B.GenTri2045
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxRecDepth 400000

#kc_repo #kc_ktree CertificateChecks.KernelMisc.GH23Lat W1
  "Certificates/Kernel/Misc/Perm/GH23Lat/data/w1.bin" 64 4 806400 11905855667202659429

namespace CertificateChecks.KernelMisc.GH23Lat

@[expose] noncomputable def cv1 (s : Nat) : Bool := covS W1 5 s

end CertificateChecks.KernelMisc.GH23Lat

#kc_slices CertificateChecks.KernelMisc.GH23Lat.CV1 CertificateChecks.KernelMisc.GH23Lat.cv1 50

end
