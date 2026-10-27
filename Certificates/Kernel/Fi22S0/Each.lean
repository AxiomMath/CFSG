module

public import Certificates.Kernel.Fi22S0.Data
public import Certificates.Data.Kernel.Fi22S0.Check
public import Certificates.Data.Kernel.Spor.Row
public import Certificates.Data.Kernel.Fi22.Orb

public section

namespace CertificateChecks.KernelFi22S0

open CFSG.KC.Loop CFSG.KC.Fi22S0 CFSG.KS.Row

@[expose] noncomputable def tb (o i : Nat) : Nat := rg (nat_lit 16) (nat_lit 65535) TF o i

@[expose] noncomputable def oi (k : Nat) : Nat :=
  tb (nat_lit 0) (Nat.mul (nat_lit 2) (Nat.sub k (nat_lit 3)))

@[expose] noncomputable def oj (k : Nat) : Nat :=
  tb (nat_lit 0) (Nat.add (Nat.mul (nat_lit 2) (Nat.sub k (nat_lit 3))) (nat_lit 1))

@[expose] noncomputable def pp (i : Nat) : Nat := tb (nat_lit 36) i

@[expose] noncomputable def pj (i : Nat) : Nat := tb (nat_lit 652) i

@[expose] noncomputable def lt (j i : Nat) : Nat :=
  tb (Nat.add (nat_lit 1268) (Nat.mul (nat_lit 616) j)) i

@[expose] noncomputable def sg (m : Nat) : Nat := tb (nat_lit 3116) m

@[expose] noncomputable def key (i : Nat) : Nat :=
  rg (nat_lit 64) (nat_lit 18446744073709551615) KF (nat_lit 0) i

@[expose] noncomputable def gR (j : Nat) : Nat :=
  RF (nIf(Nat.beq j (nat_lit 0), nat_lit 218, nIf(Nat.beq j (nat_lit 1), nat_lit 411, nat_lit 569)))

@[expose] noncomputable def k0 : Nat :=
  Nat.lor (Nat.shiftLeft (nat_lit 1) (nat_lit 12))
    (Nat.lor (Nat.shiftLeft (nat_lit 6) (nat_lit 24))
      (Nat.lor (Nat.shiftLeft (nat_lit 11) (nat_lit 36)) (Nat.shiftLeft (nat_lit 3) (nat_lit 48))))

@[expose] noncomputable def ch131101slp (k : Nat) : Bool := regC RF oi oj k

@[expose] noncomputable def ch131101base : Bool :=
  baseC RF (CFSG.Sporadic.Fi22.Native.orbEntry 0) (CFSG.Sporadic.Fi22.Native.orbEntry 1)

@[expose] noncomputable def ch131101tree (q : Nat) : Bool :=
  blkC (nat_lit 2187) (treeC key pp pj gR k0) q

@[expose] noncomputable def ch131101left (q : Nat) : Bool :=
  blkC (nat_lit 2187) (fun i => CFSG.KC.Enum.allN (nat_lit 3) fun j =>
    leftC key lt gR (nat_lit 19683) j i) q

@[expose] noncomputable def ch131101sort (q : Nat) : Bool :=
  blkC (nat_lit 2187) (sortC key sg (nat_lit 19683)) q

end CertificateChecks.KernelFi22S0

end
