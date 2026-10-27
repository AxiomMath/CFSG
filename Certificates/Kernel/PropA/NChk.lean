module

public import Certificates.Kernel.PropA.Data
public import Certificates.Kernel.PropA.NData
public import Certificates.Data.Kernel.Spor.PCos
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelPropA

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.PCos

theorem pa450010_NW1 : bAnd(Nat.beq (pa450010NW1 0) (pidn 28 5), bAnd(Nat.beq (pa450010NW1 1)
    (pa450010S1 3), bAnd(Nat.beq (pa450010NW1 2) (pcomp 28 5 (mask 5) (pa450010S1 3)
    pa450010XD.R), Nat.beq (pa450010NW1 3) pa450010XD.R))) = true := by quickRfl
theorem pa450010_NW2 : bAnd(Nat.beq (pa450010NW2 0) (pidn 28 5), bAnd(Nat.beq (pa450010NW2 1)
    (pa450010S2 3), bAnd(Nat.beq (pa450010NW2 2) (pcomp 28 5 (mask 5) (pa450010S2 3)
    pa450010XD.R), Nat.beq (pa450010NW2 3) pa450010XD.R))) = true := by quickRfl

theorem pa450010_N1_cos : cosK 28 5 (mask 5) pa450010CKX1.cnt pa450010CKX1.T pa450010J.cnt
    pa450010J.T 4 pa450010NW1 pa450010CKX1.k pa450010CKX1.G pa450010XD.R pa450010NE1 = true := by
  quickRfl
theorem pa450010_N2_cos : cosK 28 5 (mask 5) pa450010CKX2.cnt pa450010CKX2.T pa450010J.cnt
    pa450010J.T 4 pa450010NW2 pa450010CKX2.k pa450010CKX2.G pa450010XD.R pa450010NE2 = true := by
  quickRfl

end CertificateChecks.KernelPropA

end
