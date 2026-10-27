module

public import Certificates.Kernel.CU43Aut.Small
public import Certificates.Kernel.U43Rho.Data
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC3U43
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU43Rho

open CFSG.EvenSporadicStandard.M24Std.CU43 CFSG.LieType.Multipliers.U43
  CFSG.EvenSporadicStandard.Fin76b
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim
open CertificateChecks.KernelU43B CertificateChecks.KernelCU43Aut

theorem kRhoPt : allN 820 (fun i => Nat.beq (pg 10 (mask 10) (RH 0) i)
    (ptIndex (semiFun (decode i)))) = true := by
  quickRfl

theorem kRho : bAnd(Nat.beq (pc (RH 0) (RH 0)) (pidn 820 10), inPK (pc (RH 0) (TKI 5))) = true := by
  quickRfl

theorem kRhoNorm : allN 2 (fun g => inPK (pc (pc (RH 0) (C.S g)) (RH 0))) = true := by
  quickRfl

end CertificateChecks.KernelU43Rho

end
