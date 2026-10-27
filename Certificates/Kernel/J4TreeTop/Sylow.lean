module

public import Certificates.Kernel.J4TreeNode.Tabs
public import Certificates.Data.Kernel.J4TreeTopSylow
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallTree

public section

#kc_repo #kc_items_root CFSG.KC.J4TreeS.Data.sy "Certificates/Kernel/J4TreeTop/data/sylow.items" 11040 7116389027498991748

namespace CFSG.KC.J4TreeS

open CFSG.KC.J4TreeN

@[expose] noncomputable def syRec (i : Nat) : TGlob := parseG (decF 4096 (Data.sy i))

@[expose] noncomputable def syChk (i : Nat) : Bool := topGlobOK tabs i (syRec i)

set_option maxRecDepth 400000

#kc_each syChk 0 9

#kc_forall_tree sy_all (fun i => syChk i = true) 9 CFSG.KC.J4TreeS.syChk

end CFSG.KC.J4TreeS
