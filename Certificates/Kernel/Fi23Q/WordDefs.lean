module

public import Certificates.Data.Kernel.Fi23Q.Words
public import Certificates.Kernel.Fi23Q.CenDefs
public import Certificates.Kernel.Fi23Q.ChkDefs
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeKleinInputs

public section

namespace CFSG.KD.Fi23Q

open CFSG.KC.Enum CFSG.KC.Fi23K CFSG.KC.Fi23Q CFSG.KD.Fi23K
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Native

@[expose] def zR : List Nat := kleinZ.map (Nat.add 52)

@[expose] def t3R (c : Nat) : List Nat :=
  if c = 0 then [2, 3] else if c = 1 then zR else if c = 2 then [4, 5, 2, 1] else [5, 3, 7, 0, 6, 1]

@[expose] noncomputable def wordK (q c n W : Nat) : Bool := clsW H G t3R CR (nat_lit 198) q c n W

@[expose] noncomputable def zK : Bool :=
  bAnd(eqH G (zR ++ qR0) (qR0 ++ zR), bAnd(eqH G (zR ++ qR1) (qR1 ++ zR),
    eqH G (zR ++ qR2) (qR2 ++ zR)))

@[expose] noncomputable def t2K : Bool := tcB G (nat_lit 2) (nat_lit 30132)

end CFSG.KD.Fi23Q

end
