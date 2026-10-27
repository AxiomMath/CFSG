module

public import Certificates.Kernel.Fi22Twist.L5Blocks
import CFSG.Certificates.Kernel.Common.Each

public section

namespace CertificateChecks.KernelFi22Twist

open CFSG.KC.Enum CFSG.KC.Fi22Twist CFSG.KD.Fi22Twist

@[expose] noncomputable def ch431009nf_ (j : Nat) : Bool :=
  allBlk (nat_lit 0) (fun m =>
    strictB (fld(NF (Nat.add (Nat.mul (nat_lit 8) j) m), nat_lit 0, m72)) fun ci =>
    allBlk (nat_lit 0) (fun l => Nat.blt (cg ci l) (nat_lit 3510)) (nat_lit 6)) (t12 ngC j)

end CertificateChecks.KernelFi22Twist

#kc_each CertificateChecks.KernelFi22Twist.ch431009nf_ 0 5

namespace CertificateChecks.KernelFi22Twist

open CFSG.KC.Enum CFSG.KC.Fi22Twist CFSG.KD.Fi22Twist

theorem neg431009nf :
    Bool.not (strictB (Nat.lor (fld(NF (nat_lit 0), nat_lit 0, m72)) (nat_lit 4095)) fun ci =>
      allBlk (nat_lit 0) (fun l => Nat.blt (cg ci l) (nat_lit 3510)) (nat_lit 6)) = true := by
  decide +kernel

end CertificateChecks.KernelFi22Twist

end
