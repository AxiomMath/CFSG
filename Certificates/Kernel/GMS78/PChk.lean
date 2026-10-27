module

public import Certificates.Kernel.GMS78.PJ
public import Certificates.Data.GMS78RuSPrimeCheck
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelGMS78.SD

open CFSG.KC.GMS CFSG.KLie.CT CFSG.GMS78RuSP

theorem tX : czListEq XS (xPts.map fun x => x.1 ||| (x.2.1.val <<< 8) ||| (x.2.2.val <<< 11)) =
    true := by quickRfl

theorem tXs : xPts.all (fun x => decide (x.1 < 256)) = true := by quickRfl

theorem tA : kA117 mP XS JM = true := by quickRfl

theorem tL : kLists117 mP XS JM CXL F1L KL = true := by quickRfl

@[expose] noncomputable def cxF (i : Nat) : Bool := kCx mP JM (neGet 0 CXL i)
@[expose] noncomputable def f1F (i : Nat) : Bool := kF1 mP JM (neGet 0 F1L i)
@[expose] noncomputable def f3F (i : Nat) : Bool := kF3 mP JM (neGet 0 KL i)

#lc_blocks cxB cxF 240 4
#lc_blocks f1B f1F 256 32
#lc_blocks f3B f3F 16 1

end CertificateChecks.KernelGMS78.SD

end
