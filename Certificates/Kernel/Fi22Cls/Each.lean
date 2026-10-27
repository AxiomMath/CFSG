module

public import Certificates.Kernel.Fi22Cls.Data
public import Certificates.Kernel.Fi22S0.Each
public import Certificates.Data.Kernel.Fi22Cls.Check

public section

namespace CertificateChecks.KernelFi22Cls

open CFSG.KC.Enum CFSG.KC.Fi22Cls CFSG.KS.Row CertificateChecks.KernelFi22S0

@[expose] noncomputable def tc (o i : Nat) : Nat := rg (nat_lit 16) (nat_lit 65535) CF o i

@[expose] noncomputable def rep (l : Nat) : Nat := tc (nat_lit 0) l

@[expose] noncomputable def cls (l : Nat) : Nat := tc (nat_lit 4) l

@[expose] noncomputable def wo (l : Nat) : Nat := tc (nat_lit 8) l

@[expose] noncomputable def wd (t : Nat) : Nat := tc (nat_lit 12) t

@[expose] noncomputable def cX (k u : Nat) : Nat := tc (Nat.add (nat_lit 75) (Nat.mul (nat_lit 3) k)) u

@[expose] noncomputable def cQ (k u j : Nat) : Nat :=
  tc (Nat.add (nat_lit 76) (Nat.mul (nat_lit 3) k)) (Nat.add (Nat.mul (nat_lit 3) u) j)

@[expose] noncomputable def cN (k : Nat) : Nat := tc (Nat.add (nat_lit 77) (Nat.mul (nat_lit 3) k)) (nat_lit 0)

@[expose] noncomputable def cP (k : Nat) : Nat := tc (Nat.add (nat_lit 77) (Nat.mul (nat_lit 3) k)) (nat_lit 1)

@[expose] noncomputable def ct (u : Nat) : Nat := tc (nat_lit 87) u

@[expose] noncomputable def gi (j : Nat) : Nat := tc (nat_lit 88) j

@[expose] noncomputable def glob (k : Nat) : Nat :=
  List.getD [nat_lit 6228, nat_lit 19195, nat_lit 19264, nat_lit 19260] k (nat_lit 0)

@[expose] noncomputable def LJT (l : Nat) : Nat :=
  letT CFSG.KS.Fi22L.ljPacked CFSG.KS.Fi22L.slpPacked l

@[expose] noncomputable def ch13620conj (l : Nat) : Bool :=
  conjC rep cls wo wd LJT glob key gR pp pj k0 (nat_lit 19683) l

@[expose] noncomputable def ch13620rep (k : Nat) : Bool := rhoC pp pj lt (glob k)

@[expose] noncomputable def ch13620gen : Bool := genC pp pj gi (nat_lit 19683)

@[expose] noncomputable def ch13620clos (k : Nat) : Bool :=
  closC pp pj lt gi (cX k) (cQ k) (glob k) (cN k) (cP k) (nat_lit 19683)

@[expose] noncomputable def ch13620orb (u : Nat) : Bool :=
  conjgC pp pj lt ct (cX (nat_lit 0)) (glob (nat_lit 0)) (nat_lit 19683) u

end CertificateChecks.KernelFi22Cls

end
