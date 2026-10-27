module

public import Certificates.Kernel.LocalComp.SHatClosed.Data
public import Certificates.Kernel.SporSch.Ru.RowsGen
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.SHatD

theorem invOK : invC = true := by quickRfl

theorem bindOK : bindC = true := by quickRfl

theorem fixOK : f1C = true := by quickRfl

end CertificateChecks.KernelLC.SHatD

#kss_each CertificateChecks.KernelLC.SHatR CertificateChecks.KernelLC.SHatD.rowC 315

#kss_each CertificateChecks.KernelLC.SHatCI CertificateChecks.KernelLC.SHatD.ciC 315

end
