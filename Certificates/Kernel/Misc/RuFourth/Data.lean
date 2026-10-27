module

public import Certificates.Data.Kernel.Misc.RuFourth
import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_nat_items_gz CertificateChecks.KernelMisc.RuFourth "Certificates/Kernel/Misc/RuFourth/data/rho.items.gz" 227392 12847041072043873752
  C1 X2 RK0 RIK0 RK1 RIK1 RK2 RIK2

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelMisc.RuFourth

@[expose] noncomputable def RK (k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) RK0 (fun j _ => Nat.rec (motive := fun _ => Nat) RK1
    (fun _ _ => RK2) j) k

@[expose] noncomputable def RIK (k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) RIK0 (fun j _ => Nat.rec (motive := fun _ => Nat) RIK1
    (fun _ _ => RIK2) j) k

end CertificateChecks.KernelMisc.RuFourth

end
