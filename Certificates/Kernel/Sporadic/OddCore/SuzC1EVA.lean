module

public import Certificates.Kernel.Sporadic.OddCore.SuzC1EVS
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

theorem CertificateChecks.KernelSpor.SuzC1EV.kCC :
    CFSG.KC.Enum.allBlk 0 (fun k => CertificateChecks.KernelSpor.SuzC1EV.ccK
      (CertificateChecks.KernelSpor.SuzC1EV.T k)
      (CertificateChecks.KernelSpor.SuzC1EV.wg CertificateChecks.KernelSpor.SuzC1EWC k)) 512 =
    true := by
  quickRfl

end
