module

import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxRecDepth 400000

#kc_repo #kc_ktree CertificateChecks.KernelS63.ID M "Certificates/Kernel/S63K/data/imat.bin" 72 4 5012856 2968594357098023753
#kc_repo #kc_ktree CertificateChecks.KernelS63.ID X "Certificates/Kernel/S63K/data/iidx.bin" 4 4 573304 17309768287162755758

namespace CertificateChecks.KernelS63.ID

@[expose] noncomputable def G (k : Nat) : Nat := M k
@[expose] noncomputable def ZP (i : Nat) : Nat := M (8 + i)
@[expose] noncomputable def TP (i : Nat) : Nat := M (827 + i)
@[expose] noncomputable def ZQ (i : Nat) : Nat := X i
@[expose] noncomputable def ZS (i : Nat) : Nat := X (819 + i)
@[expose] noncomputable def TQ (i : Nat) : Nat := X (1638 + i)
@[expose] noncomputable def TS (i : Nat) : Nat := X (70434 + i)
@[expose] noncomputable def UT (i : Nat) : Nat := X (139230 + i)

end CertificateChecks.KernelS63.ID

end
