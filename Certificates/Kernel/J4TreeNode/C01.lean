module

public import Certificates.Kernel.J4TreeNode.Tabs
public import Certificates.Data.Kernel.J4TreeNodeChunk
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallTree
import CFSG.Certificates.Kernel.Common.Harness

public section

#kc_repo #kc_items_root CFSG.KC.J4TreeN.Data.c01f "Certificates/Kernel/J4TreeNode/data/c01.fld.items" 380814 18069326293387528838
#kc_repo #kc_items_root CFSG.KC.J4TreeN.Data.c01o "Certificates/Kernel/J4TreeNode/data/c01.off.items" 749 8130499217114579956

namespace CFSG.KC.J4TreeN

@[expose] noncomputable def rec01 (j : Nat) : NRec := parseRec (nodeFlds Data.c01f (Data.c01o j))

@[expose] noncomputable def chk01 (j : Nat) : Bool := chunkNodeOK tabs 1 rec01 j

set_option maxRecDepth 400000

#kc_each chk01 0 100

#kc_forall_tree chk01_all (fun j => chk01 j = true) 100 CFSG.KC.J4TreeN.chk01

@[expose] noncomputable def edgeN01 (j : Nat) : Bool := edgeNodeChk 1 rec01 j

#kc_each edgeN01 0 100

#kc_forall_tree edgeN01_all (fun j => edgeN01 j = true) 100 CFSG.KC.J4TreeN.edgeN01

theorem edge01 : edgeChk 1 rec01 = true := edgeChk_of_nodes edgeN01_all

end CFSG.KC.J4TreeN
