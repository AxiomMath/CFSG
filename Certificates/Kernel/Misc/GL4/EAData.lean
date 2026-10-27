module

public import Certificates.Data.Kernel.Misc.GL4Lat
public import Certificates.Data.Kernel.Misc.PermClos
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_ktree CertificateChecks.KernelMisc.GL4EA EA
  "Certificates/Kernel/Misc/GL4/EA/data/ea.bin" 4 4 80640 2785350091074399122
#kc_repo #kc_ktree CertificateChecks.KernelMisc.GL4EA EAI
  "Certificates/Kernel/Misc/GL4/EA/data/eai.bin" 4 4 80640 1975901313178735191

namespace CertificateChecks.KernelMisc.GL4EA

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc.Clos CFSG.KC.Misc.GL4

@[expose] noncomputable def eaAt (k : Nat) : Bool :=
  andB (invW (EA k) (EAI k))
    (impB (Nat.blt (Nat.succ k) (nat_lit 20160)) (Nat.blt (EA k) (EA (Nat.succ k))))

@[expose] noncomputable def eaS (s : Nat) : Bool := allR (Nat.mul (nat_lit 5040) s) (nat_lit 5040) eaAt

end CertificateChecks.KernelMisc.GL4EA

end
