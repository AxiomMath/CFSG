module

public import Certificates.Kernel.J4TreeNode.Tabs
public import Certificates.Data.Kernel.J4TreeNodeChunk
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallTree
import CFSG.Certificates.Kernel.Common.Harness

public section

#kc_repo #kc_items_root CFSG.KC.J4TreeN.Data.c12 "Certificates/Kernel/J4TreeNode/data/c12.items" 81413 4571375736479098432

namespace CFSG.KC.J4TreeN

@[expose] noncomputable def rec12 (j : Nat) : NRec := parseRec (decF 1048576 (Data.c12 j))

@[expose] noncomputable def chk12 (j : Nat) : Bool := chunkNodeOK tabs 12 rec12 j

set_option maxRecDepth 400000

#kc_each chk12 0 100

#kc_forall_tree chk12_all (fun j => chk12 j = true) 100 CFSG.KC.J4TreeN.chk12

theorem edge12 : edgeChk 12 rec12 = true := by quickRfl

end CFSG.KC.J4TreeN
