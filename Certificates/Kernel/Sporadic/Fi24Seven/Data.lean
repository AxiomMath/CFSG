module

public import Certificates.Kernel.Sporadic.Fi24Br.Data
public import Certificates.Kernel.Sporadic.Fi24Seven.Plan
public import Certificates.Kernel.Sporadic.Fi24Seven.Recs0
public import Certificates.Kernel.Sporadic.Fi24Seven.Recs1
public import Certificates.Kernel.Sporadic.Fi24Seven.Recs2
public import Certificates.Kernel.Sporadic.Fi24Seven.Recs3

public section

namespace CFSG.KD.F24S

open CFSG.KC.SlpM CFSG.KC.Loop

@[expose] noncomputable def R (r : Nat) : Nat :=
  nIf(Nat.blt r (nat_lit 512), RA r, nIf(Nat.blt r (nat_lit 1024), RB (Nat.sub r (nat_lit 512)),
    nIf(Nat.blt r (nat_lit 1536), RC (Nat.sub r (nat_lit 1024)), RD (Nat.sub r (nat_lit 1536)))))

@[expose] noncomputable def CK (k : Nat) : Bool :=
  chunkOK CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.ONE CFSG.KD.BrFi24.VLD (CFSG.KD.BrFi24.RB (nat_lit 23))
    (CFSG.KD.BrFi24.RB (nat_lit 24)) (R (nat_lit 0)) (WL (lyK k)) R (inK k) (ndK k) (ouK k) (eqK k)
    (neK k)

end CFSG.KD.F24S

end
