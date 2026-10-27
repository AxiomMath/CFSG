module

public import Certificates.Kernel.Sporadic.OddCore.SuzC1EZS
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

theorem CertificateChecks.KernelSpor.SuzC1EZ.kCos :
    CFSG.KC.Enum.allN 48 CertificateChecks.KernelSpor.SuzC1EZ.cosK = true := by
  quickRfl

end
