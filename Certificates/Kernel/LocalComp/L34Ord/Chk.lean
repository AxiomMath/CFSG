module

public import Certificates.Data.Kernel.L34FixPow
public import Certificates.Data.Kernel.L34Scan
public import Certificates.Kernel.LocalComp.L34SChk
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.L34Ord

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.L34FixPow CFSG.KC.L34Scan
open CFSG.KLie.CT (andB orB notB)

@[expose] noncomputable def ordPt (x : Nat) : Bool :=
  orB (fixPow x 3) (andB (orB (fixPow x 5) (notB (fixPow x 15)))
    (orB (fixPow x 7) (notB (fixPow x 21))))

@[expose] noncomputable def ordSl (j : Nat) : Bool :=
  allN 5 fun t => scanSl ordPt CertificateChecks.KernelLC.L34S.T 1344 (Nat.add (Nat.mul 5 j) t)

theorem k85c0 : ordSl 0 = true := by quickRfl

theorem k85c1 : ordSl 1 = true := by quickRfl

theorem k85c2 : ordSl 2 = true := by quickRfl

end CertificateChecks.KernelLC.L34Ord

end
