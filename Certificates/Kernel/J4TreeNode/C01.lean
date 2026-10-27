module

public import Certificates.Kernel.J4TreeNode.Tabs
public import Certificates.Data.Kernel.J4TreeNodeChunk
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallTree
import CFSG.Certificates.Kernel.Common.Harness

public section

#kc_repo #kc_items_root CFSG.KC.J4TreeN.Data.c01 "Certificates/Kernel/J4TreeNode/data/c01.items" 370110 17489108881630440268

namespace CFSG.KC.J4TreeN

@[expose] noncomputable def rec01 (j : Nat) : NRec := parseRec (decF 1048576 (Data.c01 j))

@[expose] noncomputable def chk01 (j : Nat) : Bool := chunkNodeOK tabs 1 rec01 j

set_option maxRecDepth 400000

#kc_each chk01 0 100

#kc_forall_tree chk01_all (fun j => chk01 j = true) 100 CFSG.KC.J4TreeN.chk01

theorem edge01 : edgeChk 1 rec01 = true := by quickRfl

end CFSG.KC.J4TreeN
