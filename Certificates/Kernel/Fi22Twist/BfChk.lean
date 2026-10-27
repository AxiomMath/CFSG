module

public import Certificates.Data.Kernel.Fi22Twist.Bf
public import Certificates.Kernel.Fi22Twist.Data
public import Certificates.Kernel.Sporadic.Fi22.X2069PT
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi22Twist

open CFSG.KC.Enum CFSG.KC.Fi22Twist CFSG.KD.Fi22Twist

@[expose] noncomputable def ch431009bf_ (k : Nat) : Bool :=
  allBlk (Nat.mul (nat_lit 48) k) (fun i => bfK BF CertificateChecks.KernelSpor.Fi22ChT.F i)
    (nat_lit 48)

theorem n431009bf_pt : Bool.not (bfK (fun k => nIf(Nat.beq k 5, Nat.add (BF k) (Nat.shiftLeft 1 24),
    BF k)) CertificateChecks.KernelSpor.Fi22ChT.F 5) = true := by quickRfl

theorem n431009bf_gen : Bool.not (bfK (fun k => nIf(Nat.beq k 5, Nat.lor (Nat.land (BF k)
    (Nat.sub (Nat.shiftLeft 1 120) 1)) (Nat.shiftLeft 0 120), BF k))
    CertificateChecks.KernelSpor.Fi22ChT.F 5) = true := by quickRfl

end CertificateChecks.KernelFi22Twist

#kc_each CertificateChecks.KernelFi22Twist.ch431009bf_ 0 15

end
