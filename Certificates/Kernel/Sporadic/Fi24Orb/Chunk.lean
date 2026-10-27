module

public import Certificates.Kernel.Sporadic.Fi24Orb.Data

public section

namespace CFSG.KD.Fi24Orb

open CFSG.KC.Fi24Orb

@[expose] noncomputable def forC (c : Nat) : Bool :=
  forOK FD CFSG.KD.Fi24Fix.S CFSG.KD.Fi24Fix.TG (nat_lit 306936) (nat_lit 64) (nat_lit 1)
    (Nat.mul (nat_lit 1024) c)

@[expose] noncomputable def inSC (c : Nat) : Bool :=
  inSOK FD CFSG.KD.Fi24Fix.S (nat_lit 31671) (Nat.mul (nat_lit 4096) c)

@[expose] noncomputable def vtC (c : Nat) : Bool :=
  vtOK VT CFSG.KD.Fi24Fix.TG VW (nat_lit 306936) (Nat.mul (nat_lit 512) c)

@[expose] noncomputable def bindC (c : Nat) : Bool :=
  bindOK OL NM NI VT CFSG.KD.Fi24Fix.TG CFSG.KD.Fi24Fix.AW (nat_lit 306936) (Nat.mul (nat_lit 512) c)

@[expose] noncomputable def slpC (c : Nat) : Bool :=
  slpOK MUL3 VLD3 RS IJ (nat_lit 120) (Nat.mul (nat_lit 16) c)

end CFSG.KD.Fi24Orb

end
