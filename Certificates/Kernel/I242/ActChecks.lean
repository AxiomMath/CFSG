module

public import Certificates.Data.Kernel.Fi22.I242
public import Certificates.Kernel.I242.YData
public import Certificates.Kernel.OmegaEight.AutChainAP
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelI242

open CFSG.KC.Enum CFSG.KC.I242 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim
open CFSG.HardMathSupport.Solomon.Coordinator

theorem kSig : sigOK (sigK i242Sigma) (sigInvK i242Sigma) = true := by quickRfl

theorem kSigInv : sigInvOK (sigK i242Sigma) (sigInvK i242Sigma) = true := by quickRfl

theorem kAct : allN 8 (fun r => bAnd(allN 120 (fun v =>
    bAnd(Nat.blt (pg 9 511 (CertificateChecks.KernelO8.AP.S r) v) 120,
    Nat.beq (pg 12 4095 (Y.S r) (pg 12 4095 (sigK i242Sigma) v))
      (pg 12 4095 (sigK i242Sigma) (pg 9 511 (CertificateChecks.KernelO8.AP.S r) v)))),
    allN 3510 (fun p => Bool.rec (motive := fun _ => Bool)
      (bIf(Nat.blt (pg 7 127 (sigInvK i242Sigma) p) 120, false, true))
      (Nat.blt (pg 7 127 (sigInvK i242Sigma) p) 120)
      (Nat.blt (pg 7 127 (sigInvK i242Sigma) (pg 12 4095 (Y.S r) p)) 120)))) = true := by
  quickRfl

end CertificateChecks.KernelI242

end
