module

public import Certificates.Kernel.J4TreeNode.Tabs
public import Certificates.Data.Kernel.J4TreeNodeChunk
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallTree
import CFSG.Certificates.Kernel.Common.Harness

public section

#kc_repo #kc_items_root CFSG.KC.J4TreeN.Data.c03f "Certificates/Kernel/J4TreeNode/data/c03.fld.items" 258289 2644840204177477089
#kc_repo #kc_items_root CFSG.KC.J4TreeN.Data.c03o "Certificates/Kernel/J4TreeNode/data/c03.off.items" 738 12745537206346275149

namespace CFSG.KC.J4TreeN

@[expose] noncomputable def rec03 (j : Nat) : NRec := parseRec (nodeFlds Data.c03f (Data.c03o j))

@[expose] noncomputable def chk03 (j : Nat) : Bool := chunkNodeOK tabs 3 rec03 j

set_option maxRecDepth 400000

#kc_each chk03 0 100

#kc_forall_tree chk03_all (fun j => chk03 j = true) 100 CFSG.KC.J4TreeN.chk03

@[expose] noncomputable def edgeN03 (j : Nat) : Bool := edgeNodeChk 3 rec03 j

#kc_each edgeN03 0 100

#kc_forall_tree edgeN03_all (fun j => edgeN03 j = true) 100 CFSG.KC.J4TreeN.edgeN03

theorem edge03 : edgeChk 3 rec03 = true := edgeChk_of_nodes edgeN03_all

end CFSG.KC.J4TreeN
