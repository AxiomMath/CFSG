module

public import Certificates.Kernel.Sporadic.OddCore.J3Cent
public import Certificates.Data.Kernel.PkPow
public import Certificates.Data.Kernel.Spor.Prim
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.OddCore

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.PkPow

theorem sz12625 : szOK 6156 13 = true := by quickRfl

@[expose] noncomputable def H12625 : Nat :=
  pcomp 6156 13 (mask 13) (J3CentP 22) (J3CentP 24)

theorem canon12625 : bAnd(canonK 6156 13 (mask 13) (6156 * 13) (J3CentP 22),
    bAnd(canonK 6156 13 (mask 13) (6156 * 13) (J3CentP 24),
      canonK 6156 13 (mask 13) (6156 * 13) (pidn 6156 13))) = true := by
  quickRfl

theorem pow9_12625 : Nat.beq (ppw 6156 13 H12625 9) (pidn 6156 13) = true := by
  quickRfl

theorem pow3_12625 : bIf(Nat.beq (ppw 6156 13 H12625 3) (pidn 6156 13), false, true) = true := by
  quickRfl

end CertificateChecks.KernelSpor.OddCore

end
