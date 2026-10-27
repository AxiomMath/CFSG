module

public import Certificates.Kernel.J4NP7850.Checks
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelJ4NP7850

open CFSG.KC.Loop CFSG.KC.J4Q CFSG.KD.J4Q CFSG.KD.J4M4F CFSG.KD.J4NP7850

theorem c7850_qlt : allR 32 (fun i => Nat.blt (getN 0 q i) (Nat.shiftLeft 1 112)) = true := by
  quickRfl

theorem c7850_Plen : Nat.beq P.length 6 = true := by quickRfl

theorem c7850_ulen : Nat.beq u.length 32 = true := by quickRfl

end CertificateChecks.KernelJ4NP7850

end
