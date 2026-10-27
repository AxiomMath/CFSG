module

public import Certificates.Kernel.Fi22Rank.Q2Data
public import Certificates.Data.Kernel.Fi22Rank.Defs
public import Certificates.Data.Kernel.Spor.Row

public section

namespace CertificateChecks.KernelFi22Rank.Q2

open CFSG.KC.Enum CFSG.KC.E27Lie CFSG.KC.Fi22Rank CFSG.KS.Row

@[expose] noncomputable def mm (X Y : Nat) : Nat :=
  pcomp (nat_lit 3510) (nat_lit 12) (nat_lit 4095) X Y

@[expose] noncomputable def ONE : Nat := pidn (nat_lit 3510) (nat_lit 12)

@[expose] noncomputable def tb (o i : Nat) : Nat := rg (nat_lit 16) (nat_lit 65535) TF o i

@[expose] noncomputable def key (i : Nat) : Nat := KF i

@[expose] noncomputable def gk (j : Nat) : Nat := KF (Nat.succ j)

@[expose] noncomputable def pp (i : Nat) : Nat := tb (nat_lit 0) i

@[expose] noncomputable def pj (i : Nat) : Nat := tb (nat_lit 23) i

@[expose] noncomputable def lt (j i : Nat) : Nat :=
  tb (Nat.add (nat_lit 46) (Nat.mul (nat_lit 23) j)) i

@[expose] noncomputable def sg (q : Nat) : Nat := tb (nat_lit 115) q

@[expose] noncomputable def W (a : Nat) : Nat := tb (nat_lit 138) a

@[expose] noncomputable def CI (a : Nat) : Nat := tb (nat_lit 161) a

@[expose] noncomputable def REP (c : Nat) : Nat := tb (nat_lit 184) c

@[expose] noncomputable def SM (c : Nat) : Nat := tb (nat_lit 186) c

@[expose] noncomputable def H (c t : Nat) : Nat :=
  tb (nat_lit 188) (Nat.add (Nat.mul (nat_lit 3) c) t)

@[expose] noncomputable def Y (c t : Nat) : Nat :=
  tb (nat_lit 194) (Nat.add (Nat.mul (nat_lit 3) c) t)

@[expose] noncomputable def BP (a : Nat) : Nat := tb (nat_lit 200) a

@[expose] noncomputable def BL (p : Nat) : Nat := tb (nat_lit 223) p

@[expose] noncomputable def GI (k : Nat) : Nat := tb (nat_lit 224) k

@[expose] noncomputable def ch431010tree (q : Nat) : Bool :=
  blkC (nat_lit 16) (nat_lit 729) (fun i => bAnd(treeC mm key pp pj gk ONE (nat_lit 3) i,
    allN (nat_lit 3) fun j => leftC mm key lt gk (nat_lit 729) j i)) q

@[expose] noncomputable def ch431010sort (q : Nat) : Bool :=
  blkC (nat_lit 16) (nat_lit 729) (sortC key sg (nat_lit 729)) q

@[expose] noncomputable def ch431010kill (q : Nat) : Bool :=
  blkC (nat_lit 16) (nat_lit 729) (fun a => bAnd(killC mm key W CI REP (nat_lit 729) (nat_lit 57) a,
    bigC CI SM BL BP (nat_lit 27) a)) q

@[expose] noncomputable def ch431010small (c : Nat) : Bool :=
  smallC mm key REP SM H Y (nat_lit 729) c

end CertificateChecks.KernelFi22Rank.Q2

end
