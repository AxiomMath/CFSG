module

public import Certificates.Data.Kernel.E6TT.RowA2
public import Certificates.Kernel.E6TT.Data
public import Certificates.Kernel.E6TT.WeylData
public import Certificates.Kernel.E6TT.RowData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelE6TT

open CFSG.KC.E6TT Certificates.Data.E6TableT

theorem mapsA2F :
    Nat.beq (enumK D.GR D.L0 D.N01 D.N02 D.N03 D.N04 D.N05 (leafKA2 W.H0 W.O0 RV.V)) 0 = true := by
  quickRfl

end CertificateChecks.KernelE6TT

end
