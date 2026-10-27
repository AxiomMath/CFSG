module

public import Certificates.Kernel.Sporadic.OddCore.SuzC1EVS
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

theorem CertificateChecks.KernelSpor.SuzC1EV.kVK0 :
    CFSG.KC.Enum.allBlk 0 CertificateChecks.KernelSpor.SuzC1EV.vK 256 = true := by
  quickRfl

end
