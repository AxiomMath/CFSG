module

public import Certificates.Kernel.J4TreeNode.Tabs
public import Certificates.Data.Kernel.J4TreeNodeChunk
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallTree
import CFSG.Certificates.Kernel.Common.Harness

public section

#kc_repo #kc_items_root CFSG.KC.J4TreeN.Data.c10f "Certificates/Kernel/J4TreeNode/data/c10.fld.items" 139034 4297590493692490656
#kc_repo #kc_items_root CFSG.KC.J4TreeN.Data.c10o "Certificates/Kernel/J4TreeNode/data/c10.off.items" 701 8778407163395421923

namespace CFSG.KC.J4TreeN

@[expose] noncomputable def rec10 (j : Nat) : NRec := parseRec (nodeFlds Data.c10f (Data.c10o j))

@[expose] noncomputable def chk10 (j : Nat) : Bool := chunkNodeOK tabs 10 rec10 j

set_option maxRecDepth 400000

#kc_each chk10 0 100

#kc_forall_tree chk10_all (fun j => chk10 j = true) 100 CFSG.KC.J4TreeN.chk10

@[expose] noncomputable def edgeN10 (j : Nat) : Bool := edgeNodeChk 10 rec10 j

#kc_each edgeN10 0 100

#kc_forall_tree edgeN10_all (fun j => edgeN10 j = true) 100 CFSG.KC.J4TreeN.edgeN10

theorem edge10 : edgeChk 10 rec10 = true := edgeChk_of_nodes edgeN10_all

end CFSG.KC.J4TreeN
