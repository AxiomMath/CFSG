module

public import CFSG.Certificates.Kernel.Bounds.Core3
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_items_root CertificateChecks.KernelE27Orth.O10p.D "Certificates/Kernel/E27Orth/data/o10p.items" 20402 14625921698047363340

namespace CertificateChecks.KernelE27Orth.O10p

@[expose] noncomputable def G (j : Nat) : Nat := D j
@[expose] noncomputable def Y (j : Nat) : Nat := D (Nat.add (nat_lit 3) j)
@[expose] noncomputable def Yi (j : Nat) : Nat := D (Nat.add (nat_lit 6) j)
@[expose] noncomputable def U : Nat := D (nat_lit 9)
@[expose] noncomputable def E (i : Nat) : Nat := D (Nat.add (nat_lit 10) i)
@[expose] noncomputable def Tr (i : Nat) : Nat := D (Nat.add (nat_lit 253) i)
@[expose] noncomputable def Ss (k : Nat) : Nat := D (Nat.add (nat_lit 496) k)
@[expose] noncomputable def Lf (q : Nat) : Nat := D (Nat.add (nat_lit 739) q)
@[expose] noncomputable def GB (j : Nat) : Nat := D (Nat.add (nat_lit 1468) j)
@[expose] noncomputable def YB (j : Nat) : Nat := D (Nat.add (nat_lit 1472) j)
@[expose] noncomputable def YBi (j : Nat) : Nat := D (Nat.add (nat_lit 1476) j)
@[expose] noncomputable def EB (i : Nat) : Nat := D (Nat.add (nat_lit 1480) i)
@[expose] noncomputable def TrB (i : Nat) : Nat := D (Nat.add (nat_lit 1561) i)
@[expose] noncomputable def SB (k : Nat) : Nat := D (Nat.add (nat_lit 1642) k)
@[expose] noncomputable def LfB (q : Nat) : Nat := D (Nat.add (nat_lit 1723) q)
@[expose] noncomputable def Wg (w : Nat) : Nat := D (Nat.add (nat_lit 2047) w)
@[expose] noncomputable def Wgi (w : Nat) : Nat := D (Nat.add (nat_lit 2178) w)
@[expose] noncomputable def Cv (i : Nat) : Nat := D (Nat.add (nat_lit 2309) i)

end CertificateChecks.KernelE27Orth.O10p

end
