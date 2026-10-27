module

public import Certificates.Kernel.Sporadic.Co2R3.Data
public import Certificates.Data.Kernel.Co2R3K
import Certificates.Kernel.Co1B.GenTri2045
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Co2R3

open CFSG.KC.Enum CFSG.KC.N3153 CFSG.KC.Co2R3 CFSG.KD.Co2R3

@[expose] noncomputable def cellB (s : Nat) : Bool :=
  strictB (PK (nat_lit 14)) fun T => cellK (nat_lit 2300) S T [0, 3, 1, 2, 522, 360] (nat_lit 3) s
    ([2300, 891, 896, 192, 10, 12].getD s (nat_lit 0))

end CertificateChecks.KernelSpor.Co2R3

#kc_slices CertificateChecks.KernelSpor.Co2R3.Cell CertificateChecks.KernelSpor.Co2R3.cellB 6

namespace CertificateChecks.KernelSpor.Co2R3

open CFSG.KC.Enum CFSG.KC.N3153 CFSG.KC.Co2R3 CFSG.KD.Co2R3

theorem inj : strictB (PK 14) (fun T => injK 2300 S T [0, 3, 1, 2, 522, 360] 3 (O 0)) = true := by
  quickRfl

theorem clab : strictB (PK 14) (fun T => clabK 2300 S T [0, 3] 3 (PK 21) [0, 1, 2, 3, 4, 5, 36]) =
    true := by
  quickRfl

end CertificateChecks.KernelSpor.Co2R3

end
