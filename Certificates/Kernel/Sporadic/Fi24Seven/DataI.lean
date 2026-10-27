module

public import Certificates.Kernel.Sporadic.Fi24Seven.Data
public import Certificates.Data.Kernel.Spor.SlpInv

public section

namespace CFSG.KD.F24S

open CFSG.KC.SlpM CFSG.KC.Loop CFSG.KC.Ord

@[expose] noncomputable def CKI (k : Nat) : Bool :=
  invOK CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.ONE CFSG.KD.BrFi24.VLD R nR pcR pnR lyK nBase k (ouK k)
    (eqK k) (neK k)

@[expose] noncomputable def GI : Bool :=
  andB (Nat.beq (CFSG.KD.BrFi24.MUL (CFSG.KD.BrFi24.RB (nat_lit 23)) (CFSG.KD.BrFi24.RB (nat_lit 23)))
      CFSG.KD.BrFi24.ONE)
    (Nat.beq (CFSG.KD.BrFi24.MUL (CFSG.KD.BrFi24.RB (nat_lit 24)) (R (nat_lit 0))) CFSG.KD.BrFi24.ONE)

end CFSG.KD.F24S

end
