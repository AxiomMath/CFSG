module

public import CFSG.Certificates.Kernel.Common.Loop
import Certificates.Kernel.Sporadic.OddCore.PEnumCmd
import Certificates.Kernel.Sporadic.OddCore.MulHCmd
meta import Certificates.Kernel.PropA.YGen

public section

#kpenum CertificateChecks.KernelPropA.pa450010XR 28 5 false CertificateChecks.KernelPropA.Gen.gXR
  CertificateChecks.KernelPropA.Gen.giXR CertificateChecks.KernelPropA.Gen.idT 2
#kpenum CertificateChecks.KernelPropA.pa450010TX1 28 5 false CertificateChecks.KernelPropA.Gen.gTX1
  CertificateChecks.KernelPropA.Gen.giTX1 CertificateChecks.KernelPropA.Gen.idT 4
#kpenum CertificateChecks.KernelPropA.pa450010TX2 28 5 false CertificateChecks.KernelPropA.Gen.gTX2
  CertificateChecks.KernelPropA.Gen.giTX2 CertificateChecks.KernelPropA.Gen.idT 4

#kfind CertificateChecks.KernelPropA.pa450010PU CertificateChecks.KernelPropA.Gen.tJ
  CertificateChecks.KernelPropA.Gen.qU
#kfind CertificateChecks.KernelPropA.pa450010PXU CertificateChecks.KernelPropA.Gen.tXR
  CertificateChecks.KernelPropA.Gen.tCDU
#kfind CertificateChecks.KernelPropA.pa450010PZ1 CertificateChecks.KernelPropA.Gen.tTX1
  CertificateChecks.KernelPropA.Gen.tY1
#kfind CertificateChecks.KernelPropA.pa450010PZ2 CertificateChecks.KernelPropA.Gen.tTX2
  CertificateChecks.KernelPropA.Gen.tY2

end
