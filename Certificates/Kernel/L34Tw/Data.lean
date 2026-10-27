module

public import Init
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_natList CertificateChecks.KernelLC.L34TwD L "Certificates/Kernel/L34Tw/d.txt" 464 17291401419098343226

namespace CertificateChecks.KernelLC.L34TwD

@[expose] noncomputable def D (k : Nat) : Nat := L.getD k 0

@[expose] noncomputable def W (k : Nat) : Nat := D (Nat.add (nat_lit 7) k)

@[expose] noncomputable def U (q : Nat) : Nat := D (Nat.add (nat_lit 135) q)

@[expose] noncomputable def Q (i : Nat) : Nat := D (Nat.add (nat_lit 3) i)

@[expose] noncomputable def I (i : Nat) : Nat := D (Nat.add (nat_lit 5) i)

end CertificateChecks.KernelLC.L34TwD

end
