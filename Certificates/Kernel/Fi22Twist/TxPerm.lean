module

public import Certificates.Data.Kernel.Fi22Rk.Defs
public import Certificates.Data.Kernel.Fi22Twist.Leaf
public import Certificates.Kernel.Fi22Twist.DfText
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi22Twist

open CFSG.KC.Enum CFSG.KC.Fi22Rk CFSG.KC.Fi22Twist

theorem ch431009tx : rowsK 3510 12 15 TX.F (rowR TX.F) = true := by quickRfl

theorem n431009tx : Bool.not (rowsK 3510 12 1 TX.F (fun k => Nat.xor (rowR TX.F k) 1)) = true := by
  quickRfl

end CertificateChecks.KernelFi22Twist

end
