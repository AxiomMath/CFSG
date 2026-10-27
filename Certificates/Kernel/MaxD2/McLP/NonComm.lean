module

public import Certificates.Kernel.MaxD2.McLP.Enum
public import Certificates.Kernel.MaxD2.McLP.Data
public import Certificates.Data.Kernel.MaxD2.Check
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMaxD2.McLP

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MaxD2 CFSG.KS.PEnum CFSG.KS.Row

@[expose] noncomputable def ncK (a b : Nat) : Bool :=
  Nat.blt a NE.k && (Nat.blt b NE.k && notInK RE.cnt RE.T
    (pcomp 275 9 (mask 9) (pcomp 275 9 (mask 9)
      (pcomp 275 9 (mask 9) (NE.G a) (NE.G b)) (NGI a)) (NGI b)))

theorem k_nc : ncK 1 3 = true := by quickRfl

end CertificateChecks.KernelMaxD2.McLP

end
