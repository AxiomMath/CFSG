module

public import Certificates.Kernel.Sporadic.OddCore.J3Cent
public import Certificates.Kernel.Census.J3.Text
public import Certificates.Data.Kernel.PkPow
public import Certificates.Data.Kernel.Spor.Prim
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.OddCore

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.PkPow CertificateChecks.KernelCensus

theorem canonJ3 : bAnd(szOK 6156 13, bAnd(canonK 6156 13 (mask 13) (6156 * 13) (J3CentP 21),
    bAnd(canonK 6156 13 (mask 13) (6156 * 13) (J3S.F 0),
    bAnd(canonK 6156 13 (mask 13) (6156 * 13) (J3S.F 1),
      canonK 6156 13 (mask 13) (6156 * 13) (pidn 6156 13))))) = true := by
  quickRfl

@[expose] noncomputable def Y129006 : Nat :=
  pcomp 6156 13 (mask 13) (J3CentP 21) (pcomp 6156 13 (mask 13) (J3S.F 1)
    (pcomp 6156 13 (mask 13) (J3CentP 21) (pcomp 6156 13 (mask 13) (J3S.F 1) (J3S.F 1))))

theorem ord129006 : bAnd(Nat.beq (ppw 6156 13 Y129006 19) (pidn 6156 13),
    bIf(Nat.beq Y129006 (pidn 6156 13), false, true)) = true := by
  quickRfl

theorem ord129006_neg :
    bIf(Nat.beq (ppw 6156 13 Y129006 18) (pidn 6156 13), false, true) = true := by
  quickRfl

end CertificateChecks.KernelSpor.OddCore

end
