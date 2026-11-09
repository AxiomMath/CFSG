module

public import Certificates.Kernel.J4TreeNode.Tabs
public import Certificates.Data.Kernel.J4TreeNodeChunk
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallTree
import CFSG.Certificates.Kernel.Common.Harness

public section

#kc_repo #kc_items_root CFSG.KC.J4TreeN.Data.c13f "Certificates/Kernel/J4TreeNode/data/c13.fld.items" 15270 9801987252628712180
#kc_repo #kc_items_root CFSG.KC.J4TreeN.Data.c13o "Certificates/Kernel/J4TreeNode/data/c13.off.items" 556 6946210903459483914

namespace CFSG.KC.J4TreeN

@[expose] noncomputable def rec13 (j : Nat) : NRec := parseRec (nodeFlds Data.c13f (Data.c13o j))

@[expose] noncomputable def chk13 (j : Nat) : Bool := chunkNodeOK tabs 13 rec13 j

set_option maxRecDepth 400000

#kc_each chk13 0 100

#kc_forall_tree chk13_all (fun j => chk13 j = true) 100 CFSG.KC.J4TreeN.chk13

@[expose] noncomputable def edgeN13 (j : Nat) : Bool := edgeNodeChk 13 rec13 j

#kc_each edgeN13 0 100

#kc_forall_tree edgeN13_all (fun j => edgeN13 j = true) 100 CFSG.KC.J4TreeN.edgeN13

theorem edge13 : edgeChk 13 rec13 = true := edgeChk_of_nodes edgeN13_all

end CFSG.KC.J4TreeN
