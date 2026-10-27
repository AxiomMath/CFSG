module

public import Certificates.Kernel.Q16J3.Data
public import Certificates.Kernel.Sporadic.OddCore.J3Cent
import all Certificates.Data.Kernel.Census.Packed
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelQ16J3

open CFSG.KC.Census

theorem q16J3_bind : ((List.range 8).all fun k => (List.range 32).all fun q =>
    Nat.blt q16J3O[q]! 6156 &&
      Nat.beq (at' 13 (CertificateChecks.KernelSpor.J3CentP (k + 1)) q16J3O[q]!)
        q16J3O[at' 5 q16J3G[k]! q]!) = true := by
  quickRfl

end CertificateChecks.KernelQ16J3
