module

public import CFSG.Certificates.Kernel.Bounds.Core3
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_items_root Certificates.KernelTower.wrL1 "Certificates/Kernel/Tower/data/wrL1.items" 27081 11481486120504593524
#kc_repo #kc_items_root Certificates.KernelTower.slL1 "Certificates/Kernel/Tower/data/slL1.items" 27157 12038217792073635425

namespace Certificates.KernelTower

@[expose] noncomputable def wrPS : Nat := wrL1.b0
@[expose] noncomputable def wrRW : Nat := wrL1.b1
@[expose] noncomputable def wrMR : Nat := wrL1.b2
@[expose] noncomputable def slPS : Nat := slL1.b0
@[expose] noncomputable def slRW : Nat := slL1.b1
@[expose] noncomputable def slMR : Nat := slL1.b2

end Certificates.KernelTower
