module

public import Certificates.Kernel.Fi22Twist.CjData
public import Certificates.Kernel.Fi22Twist.Q01Each
public import Certificates.Kernel.Fi22Twist.DfText
public import Certificates.Kernel.Fi22Rank.Q2Each
public import Certificates.Data.Kernel.Fi22Twist.Leaf
public import Certificates.Kernel.Sporadic.Fi22.X2069Final
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness

set_option Elab.async false

public section

namespace CFSG.KD.Fi22Twist

open CFSG.KC.Enum CFSG.KC.Fi22Twist CertificateChecks.KernelSpor

@[expose] noncomputable def sfG (u : Nat) : Nat :=
  nIf(Nat.blt u (nat_lit 21), CJ u,
  nIf(Nat.blt u (nat_lit 23), KQ (Nat.add (nat_lit 87) u),
  nIf(Nat.blt u (nat_lit 26), KQ (Nat.sub u (nat_lit 22)),
  nIf(Nat.blt u (nat_lit 29), KQ1 (Nat.sub u (nat_lit 25)),
  nIf(Nat.blt u (nat_lit 34),
    CertificateChecks.KernelFi22Rank.Q2.key (CertificateChecks.KernelFi22Rank.Q2.GI
      (Nat.sub u (nat_lit 29))),
    rowR CertificateChecks.KernelFi22Twist.TX.F (Nat.sub u (nat_lit 34)))))))

@[expose] noncomputable def ch431009sf (u : Nat) : Bool :=
  strictB (sfG u) fun p => bAnd(Fi22X.cn p, Fi22X.siftP p)

end CFSG.KD.Fi22Twist

#kc_each CFSG.KD.Fi22Twist.ch431009sf 0 49

namespace CFSG.KD.Fi22Twist

open CFSG.KC.Ord CFSG.KC.Enum CertificateChecks.KernelSpor

theorem neg431009sf : notB (strictB (CJ (nat_lit 0)) fun p =>
    strictB (fld(p, nat_lit 0, nat_lit 4095)) fun a => strictB (fld(p, nat_lit 12, nat_lit 4095)) fun b =>
      Fi22X.siftP (Nat.xor (Nat.xor p (Nat.lor a (Nat.shiftLeft b (nat_lit 12))))
        (Nat.lor b (Nat.shiftLeft a (nat_lit 12))))) = true := by quickRfl

end CFSG.KD.Fi22Twist

end
