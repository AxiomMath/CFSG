module

public import Certificates.Kernel.Sporadic.Fi22.X2069Final
public import Certificates.Kernel.Sporadic.Fi22.E2065
public import Certificates.Kernel.Sporadic.Fi22.E2067
public import Certificates.Kernel.Sporadic.Fi22.H2066c0
public import CFSG.Certificates.Kernel.Spor.SiftBKSound
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.N2071

open CFSG.KC.Enum CFSG.KS.Raw CFSG.KS CertificateChecks.KernelSpor CertificateChecks.KernelSpor.Fi22X

theorem pool : allN 64 (fun j => bAnd(cn (Fi22CentT.L (Nat.add 240 j)),
    bAnd(permOK 3510 12 (mask 12) (3510 * 12) (Fi22CentT.L (Nat.add 240 j))
      (inv (Fi22CentT.L (Nat.add 240 j))),
    bAnd(siftP (Fi22CentT.L (Nat.add 240 j)),
      siftBK 3510 12 (mask 12) (3510 * 12) 6 Fi22H0.S Fi22H0.SI Fi22H0.LR Fi22H0.ST 19 6 0
        (baseImK 12 (mask 12) 6 (Fi22CentT.L (Nat.add 240 j)) Fi22H0.BP))))) = true := by
  quickRfl

theorem cnA : allN 2 (fun i => cn (Fi22CentT.L (Nat.add 304 i))) = true := by quickRfl
theorem cnT0 : cn (Fi22ExtT.L 21) = true := by quickRfl
theorem comm : allN 2 (fun i => Nat.beq (c (Fi22CentT.L (Nat.add 304 i)) (Fi22ExtT.L 21))
    (c (Fi22ExtT.L 21) (Fi22CentT.L (Nat.add 304 i)))) = true := by quickRfl
theorem s0 : siftP (Fi22CentT.L 304) = true := by quickRfl
theorem s1 : bIf(siftP (Fi22CentT.L 305), false, true) = true := by quickRfl
theorem s2 : siftP (c GO (Fi22CentT.L 305)) = true := by quickRfl

end CertificateChecks.KernelSpor.N2071

end
