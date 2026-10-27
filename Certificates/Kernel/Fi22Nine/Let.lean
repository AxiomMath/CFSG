module

public import Certificates.Kernel.Fi22Nine.Defs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Fi22Nine

open CFSG.KC.Enum CFSG.KS CertificateChecks.KernelSpor

@[expose] noncomputable def letB (i n B : Nat) : Bool := allN n fun k => Nat.blt (wL i k) B

@[expose] noncomputable def letK : Bool :=
  bAnd(letB 0 51 9, bAnd(letB 1 37 9, bAnd(letB 2 67 9, bAnd(letB 3 58 9, bAnd(letB 4 74 9,
    bAnd(letB 5 1805 2, letB 6 353 2))))))

theorem lett : letK = true := by quickRfl

end CertificateChecks.KernelSpor.Fi22Nine

end
