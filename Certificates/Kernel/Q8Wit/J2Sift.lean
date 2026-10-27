module

public import Certificates.Kernel.Q8Wit.J2Data
public import Certificates.Kernel.J2Cover.AutChain
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelQ8W.J2

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CertificateChecks.KernelJ2Cover

@[expose] noncomputable def inPK (G : Nat) : Bool :=
  Nat.beq (Nat.shiftRight G (315 * 9)) 0 && allN 315 (fun i => Nat.blt (pg 9 (mask 9) G i) 315) &&
    siftK 315 9 (mask 9) (315 * 9) (pidn 315 9) PA.LR PA.TRI PA.BP 3 0 G

theorem sift : allN 2 (fun l => inPK (XG l)) = true := by quickRfl

end CertificateChecks.KernelQ8W.J2

end
