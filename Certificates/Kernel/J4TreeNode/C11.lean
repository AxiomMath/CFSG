module

public import Certificates.Kernel.J4TreeNode.Tabs
public import Certificates.Data.Kernel.J4TreeNodeChunk
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallTree
import CFSG.Certificates.Kernel.Common.Harness

public section

#kc_repo #kc_items_root CFSG.KC.J4TreeN.Data.c11f "Certificates/Kernel/J4TreeNode/data/c11.fld.items" 109343 10322301381290669820
#kc_repo #kc_items_root CFSG.KC.J4TreeN.Data.c11o "Certificates/Kernel/J4TreeNode/data/c11.off.items" 700 7165814183901774211

namespace CFSG.KC.J4TreeN

@[expose] noncomputable def rec11 (j : Nat) : NRec := parseRec (nodeFlds Data.c11f (Data.c11o j))

@[expose] noncomputable def chk11 (j : Nat) : Bool := chunkNodeOK tabs 11 rec11 j

set_option maxRecDepth 400000

#kc_each chk11 0 100

#kc_forall_tree chk11_all (fun j => chk11 j = true) 100 CFSG.KC.J4TreeN.chk11

@[expose] noncomputable def edgeN11 (j : Nat) : Bool := edgeNodeChk 11 rec11 j

#kc_each edgeN11 0 100

#kc_forall_tree edgeN11_all (fun j => edgeN11 j = true) 100 CFSG.KC.J4TreeN.edgeN11

theorem edge11 : edgeChk 11 rec11 = true := edgeChk_of_nodes edgeN11_all

end CFSG.KC.J4TreeN
