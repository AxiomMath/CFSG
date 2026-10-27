module

public import Certificates.Kernel.Fi22Twist.CjData
public import Certificates.Kernel.Fi22Twist.PrData
public import Certificates.Kernel.Fi22Twist.Data
public import Certificates.Kernel.Fi22Rank.Q2Data
public import Certificates.Data.Kernel.Fi22Twist.Conj
public import Certificates.Data.Kernel.Spor.Chain

public section

namespace CFSG.KD.Fi22Twist

open CFSG.KC.Ord CFSG.KC.Enum CFSG.KC.E27Lie CFSG.KC.Fi22Twist CFSG.KS

@[expose] noncomputable def ch431009rc (c : Nat) : Bool :=
  cjRC CertificateChecks.KernelFi22Rank.Q2.KF PM PX DF CJ RC (nat_lit 21) c

@[expose] noncomputable def ch431009cp (r : Nat) : Bool :=
  permOK (nat_lit 3510) (nat_lit 12) (mask (nat_lit 12)) (Nat.mul (nat_lit 3510) (nat_lit 12)) (CJ r)
    (pinvS (nat_lit 3510) (nat_lit 12) (mask (nat_lit 12)) (CJ r))

end CFSG.KD.Fi22Twist

end
