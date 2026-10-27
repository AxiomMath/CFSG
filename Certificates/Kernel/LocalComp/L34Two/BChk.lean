module

public import Certificates.Kernel.LocalComp.L34Two.Data
public import Certificates.Kernel.LocalComp.L34SChk
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.L34Two

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KC.BfsPin
open CFSG.KLie.CT (andB notB)

theorem kB_gens : gensK Certificates.L34TwoSig.bGens 42 6 2 L34TwoB.G = true := by quickRfl

theorem kB_hd : penumHdK (pidn 42 6) 9 9 L34TwoB.T L34TwoB.PL = true := by quickRfl

theorem kB_sl : penumSlK 42 6 (mask 6) (42 * 6) false L34TwoB.G L34TwoB.GI 2 9 L34TwoB.T L34TwoB.PL
    L34TwoB.POS L34TwoB.SRT L34TwoB.SRI 0 9 = true := by
  quickRfl

theorem kB_inv : allN 9 (fun j => andB (canonK 42 6 (mask 6) (42 * 6) (L34TwoB.BTI j))
    (Nat.beq (pcomp 42 6 (mask 6) (L34TwoB.BTI j) (L34TwoB.T j)) (pidn 42 6))) = true := by
  quickRfl

theorem kB_S : andB (Nat.beq (L34S.T 499) (L34TwoB.G 0)) (Nat.beq (L34S.T 18821) (L34TwoB.G 1)) =
    true := by
  quickRfl

theorem kNeg : notB (CFSG.KC.L34Two.sigK 42 6 (L34TwoB.G 0) (L34TwoB.G 1) L34TwoB.T L34TwoB.BTI 9
    (pidn 42 6) (L34R.T 2) 0) = true := by
  quickRfl

theorem kNeg2 : notB (CFSG.KC.L34Two.sigK 42 6 (L34TwoB.G 0) (L34TwoB.G 1) L34TwoB.T L34TwoB.BTI 9
    (pidn 42 6) (L34R.T 2) 1) = true := by
  quickRfl

end CertificateChecks.KernelLC.L34Two

end
