module

public import Certificates.Kernel.Sporadic.OddCore.SuzC1EVS
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

theorem CertificateChecks.KernelSpor.SuzC1EV.slV1 :
    CertificateChecks.KernelSpor.SuzC1EV.slV 1 = true := by
  quickRfl

end
