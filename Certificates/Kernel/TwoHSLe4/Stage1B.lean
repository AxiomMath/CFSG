module

public import Certificates.Kernel.TwoHSLe4.SO5D
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace CertificateChecks.KernelTwoHSLe4.SO5

open CFSG.EvenSporadicStandard.TwoHS

theorem b_mul : P0L.all (fun p => P0L.all fun q => P0L.contains (mulK p q)) = true := by quickRfl

theorem b_inv : P0L.all (fun p => P0L.any fun q => mulK p q == oneK) = true := by quickRfl

theorem b_inv2 : P0L.all (fun p => !(mulK p p == oneK) || decide (unpk p = fmOne) ||
    CJL.any fun e => e.1 == p) = true := by
  quickRfl

theorem b_cj : CJL.all (fun e => P0L.contains e.1 && mulK e.2.1 e.1 == mulK (SG (e.2.2 % 4)) e.2.1) =
    true := by
  quickRfl

theorem b_tau3 : P0L.all (fun p => mulK p (SG 2) == mulK (SG 2) p) = true := by quickRfl

end CertificateChecks.KernelTwoHSLe4.SO5

end
