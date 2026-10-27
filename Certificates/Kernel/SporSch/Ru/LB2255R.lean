module

public import Certificates.Kernel.SporSch.Ru.LB2255
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.SporSch.Ru.CChain
public import Certificates.Kernel.SporSch.Ru.LChain

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.RuLB

open CFSG.KC.Enum

theorem rep : allN 19 repOK = true := by quickRfl

theorem ord : allN 19 ordOK = true := by quickRfl

theorem tot : bAnd(Nat.beq (totC 0) 816, bAnd(Nat.beq (totC 1) 0, bAnd(Nat.beq (totC 2) 0,
    Nat.beq (totC 3) 4))) = true := by quickRfl

end CertificateChecks.KernelSporSch.RuLB

end
