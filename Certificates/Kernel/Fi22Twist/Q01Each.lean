module

public import Certificates.Kernel.Fi22Twist.Q01Data
public import Certificates.Kernel.Fi22Twist.Data
public import Certificates.Data.Kernel.Fi22Twist.Q01
public import Certificates.Data.Kernel.Spor.Chain

public section

namespace CFSG.KD.Fi22Twist

open CFSG.KC.Ord CFSG.KC.Enum CFSG.KC.E27Lie CFSG.KC.Fi22Twist CFSG.KS

@[expose] noncomputable def KQ1 (i : Nat) : Nat := KQ (Nat.add (nat_lit 27) i)

@[expose] noncomputable def TQ1 (i : Nat) : Nat := TQ (Nat.add (nat_lit 27) i)

@[expose] noncomputable def ch431009q (u : Nat) : Bool :=
  bIf(Nat.blt u (nat_lit 27), q01C KQ TQ DF (KQ (nat_lit 108)) (nat_lit 0) (nat_lit 27) u,
    q01C KQ1 TQ1 DF (KQ (nat_lit 109)) (nat_lit 1) (nat_lit 81) (Nat.sub u (nat_lit 27)))

@[expose] noncomputable def ch431009qp (k : Nat) : Bool :=
  strictB (KQ (Nat.add (nat_lit 108) k)) fun g =>
  permOK (nat_lit 3510) (nat_lit 12) (mask (nat_lit 12)) (Nat.mul (nat_lit 3510) (nat_lit 12)) g
    (pinvS (nat_lit 3510) (nat_lit 12) (mask (nat_lit 12)) g)

end CFSG.KD.Fi22Twist

end
