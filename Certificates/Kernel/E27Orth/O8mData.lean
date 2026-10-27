module

public import CFSG.Certificates.Kernel.Bounds.Core3
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_items_root CertificateChecks.KernelE27Orth.O8m.D "Certificates/Kernel/E27Orth/data/o8m.items" 4267 14913151006700899021

namespace CertificateChecks.KernelE27Orth.O8m

@[expose] noncomputable def G (j : Nat) : Nat := D j
@[expose] noncomputable def Y (j : Nat) : Nat := D (Nat.add (nat_lit 4) j)
@[expose] noncomputable def Yi (j : Nat) : Nat := D (Nat.add (nat_lit 8) j)
@[expose] noncomputable def U : Nat := D (nat_lit 12)
@[expose] noncomputable def E (i : Nat) : Nat := D (Nat.add (nat_lit 13) i)
@[expose] noncomputable def Tr (i : Nat) : Nat := D (Nat.add (nat_lit 94) i)
@[expose] noncomputable def Ss (k : Nat) : Nat := D (Nat.add (nat_lit 175) k)
@[expose] noncomputable def Lf (q : Nat) : Nat := D (Nat.add (nat_lit 256) q)
@[expose] noncomputable def Fl (s : Nat) : Nat := D (Nat.add (nat_lit 580) s)
@[expose] noncomputable def Fm (i : Nat) : Nat := D (Nat.add (nat_lit 588) i)
@[expose] noncomputable def Pw (q : Nat) : Nat := D (Nat.add (nat_lit 669) q)

end CertificateChecks.KernelE27Orth.O8m

end
