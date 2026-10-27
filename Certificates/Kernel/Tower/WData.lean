module

public import CFSG.Certificates.Kernel.Bounds.Core3
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_items_root Certificates.KernelTower.wrW "Certificates/Kernel/Tower/data/wrW.items" 21068 9733318206456611292
#kc_repo #kc_items_root Certificates.KernelTower.slW "Certificates/Kernel/Tower/data/slW.items" 21068 8578743947869927605

namespace Certificates.KernelTower

@[expose] noncomputable def wrLP : Nat := wrW.b0
@[expose] noncomputable def wrSM : Nat := wrW.b1
@[expose] noncomputable def wrAC : Nat := wrW.b2
@[expose] noncomputable def slLP : Nat := slW.b0
@[expose] noncomputable def slSM : Nat := slW.b1
@[expose] noncomputable def slAC : Nat := slW.b2

end Certificates.KernelTower
