module

public import Certificates.Kernel.Misc.Perm.GH23LatData
public import Certificates.Kernel.Co1B.GenTri2045
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxRecDepth 400000

#kc_repo #kc_ktree CertificateChecks.KernelMisc.GH23Lat W2
  "Certificates/Kernel/Misc/Perm/GH23Lat/data/w2.bin" 64 4 806400 11442453231248888012

namespace CertificateChecks.KernelMisc.GH23Lat

@[expose] noncomputable def cv2 (s : Nat) : Bool := covS W2 10 s

end CertificateChecks.KernelMisc.GH23Lat

#kc_slices CertificateChecks.KernelMisc.GH23Lat.CV2 CertificateChecks.KernelMisc.GH23Lat.cv2 50

end
