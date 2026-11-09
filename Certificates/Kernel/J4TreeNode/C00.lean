module

public import Certificates.Kernel.J4TreeNode.Tabs
public import Certificates.Data.Kernel.J4TreeNodeChunk
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallTree
import CFSG.Certificates.Kernel.Common.Harness

public section

#kc_repo #kc_items_root CFSG.KC.J4TreeN.Data.c00f "Certificates/Kernel/J4TreeNode/data/c00.fld.items" 542957 3883729899267496393
#kc_repo #kc_items_root CFSG.KC.J4TreeN.Data.c00o "Certificates/Kernel/J4TreeNode/data/c00.off.items" 758 353791865081625250

namespace CFSG.KC.J4TreeN

@[expose] noncomputable def rec00 (j : Nat) : NRec := parseRec (nodeFlds Data.c00f (Data.c00o j))

@[expose] noncomputable def chk00 (j : Nat) : Bool := chunkNodeOK tabs 0 rec00 j

set_option maxRecDepth 400000

#kc_each chk00 0 100

#kc_forall_tree chk00_all (fun j => chk00 j = true) 100 CFSG.KC.J4TreeN.chk00

@[expose] noncomputable def edgeN00 (j : Nat) : Bool := edgeNodeChk 0 rec00 j

#kc_each edgeN00 0 100

#kc_forall_tree edgeN00_all (fun j => edgeN00 j = true) 100 CFSG.KC.J4TreeN.edgeN00

theorem edge00 : edgeChk 0 rec00 = true := edgeChk_of_nodes edgeN00_all

end CFSG.KC.J4TreeN
