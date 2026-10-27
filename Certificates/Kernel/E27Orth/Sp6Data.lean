module

public import CFSG.Certificates.Kernel.Bounds.Core3
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_items_root CertificateChecks.KernelE27Orth.Sp6.D "Certificates/Kernel/E27Orth/data/sp6.items" 3083 10787614969664903459

namespace CertificateChecks.KernelE27Orth.Sp6

@[expose] noncomputable def G (j : Nat) : Nat := D j
@[expose] noncomputable def J : Nat := D (nat_lit 2)
@[expose] noncomputable def E (i : Nat) : Nat := D (Nat.add (nat_lit 3) i)
@[expose] noncomputable def Tr (i : Nat) : Nat := D (Nat.add (nat_lit 84) i)
@[expose] noncomputable def Ss (k : Nat) : Nat := D (Nat.add (nat_lit 165) k)
@[expose] noncomputable def Lf (q : Nat) : Nat := D (Nat.add (nat_lit 246) q)
@[expose] noncomputable def Fl (s : Nat) : Nat := D (Nat.add (nat_lit 408) s)
@[expose] noncomputable def Fm (i : Nat) : Nat := D (Nat.add (nat_lit 416) i)
@[expose] noncomputable def Pw (q : Nat) : Nat := D (Nat.add (nat_lit 497) q)

end CertificateChecks.KernelE27Orth.Sp6

end
