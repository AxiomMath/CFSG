module

public import Certificates.Kernel.J4TreeNode.Tabs
public import Certificates.Data.Kernel.J4TreeNodeChunk
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallTree
import CFSG.Certificates.Kernel.Common.Harness

public section

#kc_repo #kc_items_root CFSG.KC.J4TreeN.Data.c11 "Certificates/Kernel/J4TreeNode/data/c11.items" 107195 1431184221457509232

namespace CFSG.KC.J4TreeN

@[expose] noncomputable def rec11 (j : Nat) : NRec := parseRec (decF 1048576 (Data.c11 j))

@[expose] noncomputable def chk11 (j : Nat) : Bool := chunkNodeOK tabs 11 rec11 j

set_option maxRecDepth 400000

#kc_each chk11 0 100

#kc_forall_tree chk11_all (fun j => chk11 j = true) 100 CFSG.KC.J4TreeN.chk11

theorem edge11 : edgeChk 11 rec11 = true := by quickRfl

end CFSG.KC.J4TreeN
