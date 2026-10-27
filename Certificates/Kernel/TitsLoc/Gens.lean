module

public import Certificates.Kernel.TwoF4Lie.Checks
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelTitsLoc

open CFSG.KC.Enum CFSG.KS CFSG.KC.TwoF4LieK CertificateChecks.KernelTwoF4Lie

theorem ch4182_gens : bAnd(Nat.beq (mul (F 0) (F 0)) idP, bAnd(Nat.beq (mul (F 2) (F 2)) idP,
    Nat.beq (mul (F 3) (F 3)) idP)) = true := by quickRfl

end CertificateChecks.KernelTitsLoc

end
