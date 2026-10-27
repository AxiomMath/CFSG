module

public import Certificates.Kernel.Misc.Perm.GH23LatData
public import Certificates.Kernel.Co1B.GenTri2045
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxRecDepth 400000

#kc_repo #kc_ktree CertificateChecks.KernelMisc.GH23Lat W4
  "Certificates/Kernel/Misc/Perm/GH23Lat/data/w4.bin" 64 4 806400 11206580492411146868

namespace CertificateChecks.KernelMisc.GH23Lat

@[expose] noncomputable def cv4 (s : Nat) : Bool := covS W4 20 s

end CertificateChecks.KernelMisc.GH23Lat

#kc_slices CertificateChecks.KernelMisc.GH23Lat.CV4 CertificateChecks.KernelMisc.GH23Lat.cv4 50

end
