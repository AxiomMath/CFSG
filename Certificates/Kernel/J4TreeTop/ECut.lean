module

public import Certificates.Kernel.J4TreeNode.Tabs
public import Certificates.Data.Kernel.J4TreeTopEClass
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallTree

public section

#kc_repo #kc_items_root CFSG.KC.J4TreeT.Data.ec "Certificates/Kernel/J4TreeTop/data/ecut.items" 36466 4476087358421924018

namespace CFSG.KC.J4TreeT

open CFSG.KC.J4TreeN

@[expose] noncomputable def ecRec (e : Nat) : List Nat := decF 4096 (Data.ec e)

@[expose] noncomputable def ecChk (e : Nat) : Bool := eclassOK tabs 1131 e (ecRec e)

set_option maxRecDepth 400000

#kc_each ecChk 0 1024

#kc_forall_tree ec_all (fun e => ecChk e = true) 1024 CFSG.KC.J4TreeT.ecChk

end CFSG.KC.J4TreeT
