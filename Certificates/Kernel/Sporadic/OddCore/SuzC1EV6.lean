module

public import Certificates.Kernel.Sporadic.OddCore.SuzC1EVS
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

theorem CertificateChecks.KernelSpor.SuzC1EV.slV6 :
    CertificateChecks.KernelSpor.SuzC1EV.slV 6 = true := by
  quickRfl

end
