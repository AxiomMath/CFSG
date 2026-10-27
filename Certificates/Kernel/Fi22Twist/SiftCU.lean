module

public import Certificates.Kernel.Fi22Twist.L5Data
public import Certificates.Data.Kernel.Spor.Chain
public import Certificates.Kernel.Sporadic.Fi22.X2069Final
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness

set_option Elab.async false

public section

namespace CFSG.KD.Fi22Twist

open CFSG.KC.Enum CFSG.KS CertificateChecks.KernelSpor

@[expose] noncomputable def sfCU (u : Nat) : Nat :=
  nIf(Nat.blt u (nat_lit 23), CG u, UG (Nat.sub u (nat_lit 23)))

@[expose] noncomputable def ch431009su (u : Nat) : Bool :=
  strictB (sfCU u) fun p =>
    bAnd(permOK (nat_lit 3510) (nat_lit 12) (mask (nat_lit 12)) (Nat.mul (nat_lit 3510) (nat_lit 12)) p
      (pinvS (nat_lit 3510) (nat_lit 12) (mask (nat_lit 12)) p),
      bAnd(Fi22X.cn p, Fi22X.siftP p))

end CFSG.KD.Fi22Twist

#kc_each CFSG.KD.Fi22Twist.ch431009su 0 48

namespace CFSG.KD.Fi22Twist

open CFSG.KC.Ord CFSG.KC.Enum CFSG.KS CertificateChecks.KernelSpor

theorem neg431009su : notB (strictB (CG (nat_lit 0)) fun p =>
    strictB (fld(p, nat_lit 0, nat_lit 4095)) fun a => strictB (fld(p, nat_lit 12, nat_lit 4095)) fun b =>
      Fi22X.siftP (Nat.xor (Nat.xor p (Nat.lor a (Nat.shiftLeft b (nat_lit 12))))
        (Nat.lor b (Nat.shiftLeft a (nat_lit 12))))) = true := by quickRfl

theorem neg431009sup : notB (strictB (UG (nat_lit 0)) fun p =>
    strictB (Nat.lor (Nat.xor p (fld(p, nat_lit 0, nat_lit 4095))) (fld(p, nat_lit 12, nat_lit 4095)))
      fun q => permOK (nat_lit 3510) (nat_lit 12) (mask (nat_lit 12)) (Nat.mul (nat_lit 3510) (nat_lit 12)) q
        (pinvS (nat_lit 3510) (nat_lit 12) (mask (nat_lit 12)) q)) = true := by quickRfl

end CFSG.KD.Fi22Twist

end
