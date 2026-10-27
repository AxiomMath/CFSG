module

public import Certificates.Kernel.Fi23Q.WordDefs

public section

namespace CFSG.KD.Fi23Q

open CFSG.KC.Enum CFSG.KC.Fi23K CFSG.KD.Fi23K

@[expose] noncomputable def fixB (c x : Nat) : Bool :=
  bAnd(Nat.blt x (nat_lit 31671), Nat.beq (wv G (t3R c) x) x)

@[expose] noncomputable def fixK : Bool :=
  bAnd(fixB (nat_lit 0) (nat_lit 106), bAnd(fixB (nat_lit 1) (nat_lit 216),
    bAnd(fixB (nat_lit 2) (nat_lit 544), fixB (nat_lit 3) (nat_lit 8))))

@[expose] noncomputable def negT3Fix : Bool := !fixB (nat_lit 0) (nat_lit 107)

end CFSG.KD.Fi23Q

end
