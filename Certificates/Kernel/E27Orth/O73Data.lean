module

public import CFSG.Certificates.Kernel.Bounds.Core3
public import CFSG.Certificates.Kernel.Orders.Mat
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_items_root CertificateChecks.KernelE27Orth.O73.D "Certificates/Kernel/E27Orth/data/o73.items" 1282821 8213933142946479144

namespace CertificateChecks.KernelE27Orth.O73

@[expose] noncomputable def L : Nat := D (nat_lit 0)
@[expose] noncomputable def H : Nat := D (nat_lit 1)
@[expose] noncomputable def CM : Nat := D (nat_lit 2)
@[expose] noncomputable def RM : Nat := D (nat_lit 3)
@[expose] noncomputable def ONE : Nat := D (nat_lit 4)
@[expose] noncomputable def LV : Nat := D (nat_lit 5)
@[expose] noncomputable def HV : Nat := D (nat_lit 6)
@[expose] noncomputable def G (j : Nat) : Nat := D (Nat.add (nat_lit 7) j)
@[expose] noncomputable def Y (j : Nat) : Nat := D (Nat.add (nat_lit 10) j)
@[expose] noncomputable def E (i : Nat) : Nat := D (Nat.add (nat_lit 13) i)
@[expose] noncomputable def Tr (i : Nat) : Nat := D (Nat.add (nat_lit 19696) i)
@[expose] noncomputable def Ss (k : Nat) : Nat := D (Nat.add (nat_lit 39379) k)
@[expose] noncomputable def W (i : Nat) : Nat := D (Nat.add (nat_lit 59062) i)
@[expose] noncomputable def Rp (r : Nat) : Nat := D (Nat.add (nat_lit 78745) r)
@[expose] noncomputable def Cm (q : Nat) : Nat := D (Nat.add (nat_lit 78909) q)

@[expose] noncomputable def mulO (A B : Nat) : Nat := CFSG.KC.Ord.mulR 3 6 42 7 3 L H CM RM A B
@[expose] noncomputable def cnO (X : Nat) : Bool := CFSG.KC.Ord.validM 3 294 L H X

end CertificateChecks.KernelE27Orth.O73

end
