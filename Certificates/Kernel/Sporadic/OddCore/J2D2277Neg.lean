module

public import Certificates.Kernel.Sporadic.OddCore.J2D2277Check
public import CFSG.Certificates.Kernel.Lie.CT.Core
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.J2DCnt.Neg

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch
open CFSG.KLie.CT (notB)
open CertificateChecks.KernelSpor.J2DCnt

theorem sum11 : notB (Nat.beq (sumN (rcnt (KernelSporSch.PJ2.LR 0)) J2DC.CS) 11) = true := by
  quickRfl

theorem canon : notB (canonL 315 9 [Nat.shiftLeft 1 (315 * 9)]) = true := by quickRfl

theorem comm : notB (commK 315 9 [KernelSpor.J2D.GI 0] [KernelSpor.J2D.GI 1]) = true := by
  quickRfl

end CertificateChecks.KernelSpor.J2DCnt.Neg

end
