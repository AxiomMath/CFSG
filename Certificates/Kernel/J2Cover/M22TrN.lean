module

public import Certificates.Kernel.J2Cover.M22TrK
public import Certificates.Kernel.LocalComp.BlockGen
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ2Cover

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def fR7P (m : Nat) : Bool := fR7 (R7P 0) m

@[expose] noncomputable def fT7P (m : Nat) : Bool := fT7 (R7P 0) m

#lc_blocks R7B fR7P 16384 1024

#lc_blocks TPB fT7P 384 16

theorem negR7 : (!fR7 (Nat.xor (R7P 0) 1) 0) = true := by quickRfl

theorem negCol : (!(strictB (xrN (stR (R7P 0) (DP 1) (DI 1) (DP 5))) fun v =>
    hOK v 2 5 0 && hOK v 2 5 1 && hOK v 2 5 2 && hOK v 2 5 3 && hOK v 2 5 4 && hOK v 2 5 5 &&
      fOK v 2 5)) = true := by quickRfl

end CertificateChecks.KernelJ2Cover

end
