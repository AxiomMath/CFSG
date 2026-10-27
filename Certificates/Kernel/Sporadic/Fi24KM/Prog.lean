module

public import Certificates.Kernel.Sporadic.Fi24KM.Data

public section

namespace CFSG.KD.KMFi24

@[expose] noncomputable def sC (k : Nat) : Bool :=
  CFSG.KC.Ord.progOK CFSG.KD.BrFi24.RB 11 RS CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.ONE (PS k) (RS k)

@[expose] noncomputable def rC (j : Nat) : Bool :=
  CFSG.KC.Ord.progOK CFSG.KD.BrFi24.RB 11 RS CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.ONE (QR j)
    CFSG.KD.BrFi24.ONE

@[expose] noncomputable def mC (j : Nat) : Bool :=
  CFSG.KC.Ord.notB (Nat.beq (CFSG.KC.Ord.progTop CFSG.KD.BrFi24.RB (nat_lit 11) RS
    CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.ONE (QM j)) CFSG.KD.BrFi24.ONE)

end CFSG.KD.KMFi24

end
