module

public import Certificates.Kernel.J4TreeNode.Tabs
public import Certificates.Data.Kernel.J4TreeNodeChunk
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallTree
import CFSG.Certificates.Kernel.Common.Harness

public section

#kc_repo #kc_items_root CFSG.KC.J4TreeN.Data.c04f "Certificates/Kernel/J4TreeNode/data/c04.fld.items" 214960 8020401144004127296
#kc_repo #kc_items_root CFSG.KC.J4TreeN.Data.c04o "Certificates/Kernel/J4TreeNode/data/c04.off.items" 736 2243539548535216676

namespace CFSG.KC.J4TreeN

@[expose] noncomputable def rec04 (j : Nat) : NRec := parseRec (nodeFlds Data.c04f (Data.c04o j))

@[expose] noncomputable def chk04 (j : Nat) : Bool := chunkNodeOK tabs 4 rec04 j

set_option maxRecDepth 400000

#kc_each chk04 0 100

#kc_forall_tree chk04_all (fun j => chk04 j = true) 100 CFSG.KC.J4TreeN.chk04

@[expose] noncomputable def edgeN04 (j : Nat) : Bool := edgeNodeChk 4 rec04 j

#kc_each edgeN04 0 100

#kc_forall_tree edgeN04_all (fun j => edgeN04 j = true) 100 CFSG.KC.J4TreeN.edgeN04

theorem edge04 : edgeChk 4 rec04 = true := edgeChk_of_nodes edgeN04_all

end CFSG.KC.J4TreeN
