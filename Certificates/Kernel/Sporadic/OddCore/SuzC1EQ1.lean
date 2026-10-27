module

public import Certificates.Kernel.Sporadic.OddCore.SuzC1EZS
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

theorem CertificateChecks.KernelSpor.SuzC1EZ.slQ1 :
    CertificateChecks.KernelSpor.SuzC1EZ.slQ 96 96 = true := by
  quickRfl

end
