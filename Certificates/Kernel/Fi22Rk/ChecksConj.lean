module

public import Certificates.Kernel.Fi22Rk.Data
public import Certificates.Data.Kernel.Fi22Rk.Defs
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi22Rk.K

open CFSG.KC.Enum CFSG.KC.Fi22Rk CertificateChecks.KernelFi22Rk

@[expose] noncomputable def conj0 (c : Nat) : Bool := conjC 3510 12 D.GK D.MUK D.IK 0 c

@[expose] noncomputable def conj1 (c : Nat) : Bool := conjC 3510 12 D.GK D.MUK D.IK 1 c

open CFSG.KLie.CT (notB) in
theorem negConj : notB (conjAt 3510 12 D.GK (fun l => Nat.add (D.MUK l) (nat_lit 1)) D.IK 0 0) =
    true := by
  quickRfl

end CertificateChecks.KernelFi22Rk.K

#kc_each CertificateChecks.KernelFi22Rk.K.conj0 0 16
#kc_each CertificateChecks.KernelFi22Rk.K.conj1 0 16

end
