module

public import Certificates.Kernel.J4TreeNode.Tabs
public import Certificates.Data.Kernel.J4TreeNodeChunk
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallTree
import CFSG.Certificates.Kernel.Common.Harness

public section

#kc_repo #kc_items_root CFSG.KC.J4TreeN.Data.c12f "Certificates/Kernel/J4TreeNode/data/c12.fld.items" 82945 4028138385219494313
#kc_repo #kc_items_root CFSG.KC.J4TreeN.Data.c12o "Certificates/Kernel/J4TreeNode/data/c12.off.items" 700 4143424443250212120

namespace CFSG.KC.J4TreeN

@[expose] noncomputable def rec12 (j : Nat) : NRec := parseRec (nodeFlds Data.c12f (Data.c12o j))

@[expose] noncomputable def chk12 (j : Nat) : Bool := chunkNodeOK tabs 12 rec12 j

set_option maxRecDepth 400000

#kc_each chk12 0 100

#kc_forall_tree chk12_all (fun j => chk12 j = true) 100 CFSG.KC.J4TreeN.chk12

@[expose] noncomputable def edgeN12 (j : Nat) : Bool := edgeNodeChk 12 rec12 j

#kc_each edgeN12 0 100

#kc_forall_tree edgeN12_all (fun j => edgeN12 j = true) 100 CFSG.KC.J4TreeN.edgeN12

theorem edge12 : edgeChk 12 rec12 = true := edgeChk_of_nodes edgeN12_all

end CFSG.KC.J4TreeN
