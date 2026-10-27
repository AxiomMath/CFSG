module

public import Certificates.Kernel.AE6Q8.Chain
public meta import Certificates.Kernel.AE6Q8.Chain
public import Certificates.Data.Kernel.SporSch.ClsAll
public meta import Certificates.Kernel.SporSch.GenClsAll
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.SporSch.GenClsAll

public section

set_option maxRecDepth 400000

#kss_ptcntn CertificateChecks.KernelO8Sq.O8SqN CertificateChecks.KernelAE6Q8.SC 360 9
  CertificateChecks.KernelAE6Q8.strongS CertificateChecks.KernelAE6Q8.baseS 4

namespace CertificateChecks.KernelO8Sq

theorem ordK_SC : CFSG.KS.SporSch.MOC.ordK CertificateChecks.KernelAE6Q8.SC.LR 5 = 4096 := by
  decide +kernel

end CertificateChecks.KernelO8Sq

end
