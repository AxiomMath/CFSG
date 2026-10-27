module

public import CFSG.Certificates.Kernel.Bounds.Core3
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_items_root CertificateChecks.KernelE27Orth.O8p.D "Certificates/Kernel/E27Orth/data/o8p.items" 18645 12408276799234102568

namespace CertificateChecks.KernelE27Orth.O8p

@[expose] noncomputable def G (j : Nat) : Nat := D j
@[expose] noncomputable def Y (j : Nat) : Nat := D (Nat.add (nat_lit 4) j)
@[expose] noncomputable def Yi (j : Nat) : Nat := D (Nat.add (nat_lit 8) j)
@[expose] noncomputable def U : Nat := D (nat_lit 12)
@[expose] noncomputable def E (i : Nat) : Nat := D (Nat.add (nat_lit 13) i)
@[expose] noncomputable def Tr (i : Nat) : Nat := D (Nat.add (nat_lit 256) i)
@[expose] noncomputable def Ss (k : Nat) : Nat := D (Nat.add (nat_lit 499) k)
@[expose] noncomputable def Lf (q : Nat) : Nat := D (Nat.add (nat_lit 742) q)
@[expose] noncomputable def GB (j : Nat) : Nat := D (Nat.add (nat_lit 1714) j)
@[expose] noncomputable def YB (j : Nat) : Nat := D (Nat.add (nat_lit 1718) j)
@[expose] noncomputable def YBi (j : Nat) : Nat := D (Nat.add (nat_lit 1722) j)
@[expose] noncomputable def EB (i : Nat) : Nat := D (Nat.add (nat_lit 1726) i)
@[expose] noncomputable def TrB (i : Nat) : Nat := D (Nat.add (nat_lit 1807) i)
@[expose] noncomputable def SB (k : Nat) : Nat := D (Nat.add (nat_lit 1888) k)
@[expose] noncomputable def LfB (q : Nat) : Nat := D (Nat.add (nat_lit 1969) q)
@[expose] noncomputable def Wg (w : Nat) : Nat := D (Nat.add (nat_lit 2293) w)
@[expose] noncomputable def Wgi (w : Nat) : Nat := D (Nat.add (nat_lit 2424) w)
@[expose] noncomputable def Cv (i : Nat) : Nat := D (Nat.add (nat_lit 2555) i)

end CertificateChecks.KernelE27Orth.O8p

end
