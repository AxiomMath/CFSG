module

public import Certificates.Kernel.Sporadic.Fi24Br.Data

public section

namespace CFSG.KD.BrFi24

@[expose] noncomputable def ivC (g : Nat) : Bool :=
  CFSG.KC.Ord.andB (VLD (RB (Nat.add (Nat.succ (nat_lit 11)) g)))
    (Nat.beq (MUL (RB (Nat.succ g)) (RB (Nat.add (Nat.succ (nat_lit 11)) g))) ONE)

@[expose] noncomputable def sC (k : Nat) : Bool :=
  CFSG.KC.Ord.progOK RB 11 RS MUL ONE (PS k) (RS k)

@[expose] noncomputable def rC (j : Nat) : Bool :=
  CFSG.KC.Ord.progOK RB 11 RS MUL ONE (PR j) ONE

end CFSG.KD.BrFi24

end
