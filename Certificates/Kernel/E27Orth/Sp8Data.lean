module

public import CFSG.Certificates.Kernel.Bounds.Core3
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_items_root CertificateChecks.KernelE27Orth.Sp8.D "Certificates/Kernel/E27Orth/data/sp8.items" 15677 8603399676321056564

namespace CertificateChecks.KernelE27Orth.Sp8

@[expose] noncomputable def G (j : Nat) : Nat := D j
@[expose] noncomputable def J : Nat := D (nat_lit 3)
@[expose] noncomputable def E (i : Nat) : Nat := D (Nat.add (nat_lit 4) i)
@[expose] noncomputable def Tr (i : Nat) : Nat := D (Nat.add (nat_lit 247) i)
@[expose] noncomputable def Ss (k : Nat) : Nat := D (Nat.add (nat_lit 490) k)
@[expose] noncomputable def Lf (q : Nat) : Nat := D (Nat.add (nat_lit 733) q)
@[expose] noncomputable def GB (j : Nat) : Nat := D (Nat.add (nat_lit 1462) j)
@[expose] noncomputable def EB (i : Nat) : Nat := D (Nat.add (nat_lit 1466) i)
@[expose] noncomputable def TrB (i : Nat) : Nat := D (Nat.add (nat_lit 1547) i)
@[expose] noncomputable def SB (k : Nat) : Nat := D (Nat.add (nat_lit 1628) k)
@[expose] noncomputable def LfB (q : Nat) : Nat := D (Nat.add (nat_lit 1709) q)
@[expose] noncomputable def Wg (w : Nat) : Nat := D (Nat.add (nat_lit 2033) w)
@[expose] noncomputable def Cv (i : Nat) : Nat := D (Nat.add (nat_lit 2164) i)

end CertificateChecks.KernelE27Orth.Sp8

end
