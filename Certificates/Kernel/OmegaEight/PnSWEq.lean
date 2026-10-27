module

public import Certificates.Kernel.OmegaEight.PlusNodeData
public import Certificates.Data.Kernel.O8.NodeM
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelO8

theorem PnSW_eq : PnSW = CFSG.KC.O8.swarK := by
  have h : (PnSW == CFSG.KC.O8.swarK) = true := by quickRfl
  exact eq_of_beq h

end CertificateChecks.KernelO8
