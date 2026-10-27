module

public import Certificates.Kernel.Fi22S0.Each
public import Certificates.Kernel.Fi22S0.KillData
public import Certificates.Data.Kernel.Fi22S0.Kill

public section

namespace CertificateChecks.KernelFi22S0

open CFSG.KC.Loop CFSG.KC.Fi22S0 CFSG.KS.Row

@[expose] noncomputable def xb (o i : Nat) : Nat := rg (nat_lit 16) (nat_lit 65535) XF o i

@[expose] noncomputable def kw (a : Nat) : Nat := xb (nat_lit 0) a

@[expose] noncomputable def kc (a : Nat) : Nat := xb (nat_lit 616) a

@[expose] noncomputable def krep (r : Nat) : Nat := xb (nat_lit 1232) r

@[expose] noncomputable def kcw (r k : Nat) : Nat :=
  xb (nat_lit 1236) (Nat.add (Nat.mul (nat_lit 81) r) k)

@[expose] noncomputable def ch131101kill (q : Nat) : Bool :=
  blkC (nat_lit 2187) (killC pp pj lt kw kc krep (nat_lit 19683) (nat_lit 126)) q

@[expose] noncomputable def ch131101rep (q : Nat) : Bool :=
  blkC (nat_lit 14) (repC pp pj lt krep kcw (nat_lit 19683) (nat_lit 81)) q

end CertificateChecks.KernelFi22S0

end
