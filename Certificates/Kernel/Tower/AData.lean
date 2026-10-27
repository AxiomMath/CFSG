module

public import CFSG.Certificates.Kernel.Bounds.Core3
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_items_root Certificates.KernelTower.slA "Certificates/Kernel/Tower/data/slA.items" 557446 1886248387421263250
#kc_repo #kc_items_root Certificates.KernelTower.wrA "Certificates/Kernel/Tower/data/wrA.items" 1606791 3338752438937365818

namespace Certificates.KernelTower

@[expose] def wGS : Nat := 9008573661052992
@[expose] noncomputable def slPT : Nat := slA.b0
@[expose] noncomputable def slIM : Nat := slA.b1
@[expose] noncomputable def wrPT : Nat := wrA.b0
@[expose] noncomputable def wrIM : Nat := wrA.b1

end Certificates.KernelTower
