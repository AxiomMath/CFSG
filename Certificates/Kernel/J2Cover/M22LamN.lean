module

public import Certificates.Kernel.J2Cover.M22LamK
public import Certificates.Kernel.LocalComp.BlockGen
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ2Cover

open CFSG.KC.Enum CFSG.KS

#lc_blocks ch10022LT fLTP 16384 1024

#lc_blocks ch10022BI fBIP 128 128

#lc_blocks ch10022SI fSIP 4725 1024

#lc_blocks ch10022LY fLYP 128 4

theorem negLT : (!fLT (Nat.xor (LTP 0) 128) (LTP 2) 0) = true := by quickRfl

theorem negLY : (!fLY (LTP 0) (Nat.xor (LTP 1) 128) 1) = true := by quickRfl

end CertificateChecks.KernelJ2Cover

end
