module

public import Certificates.Kernel.J4TreeNode.Tabs
public import Certificates.Data.Kernel.J4TreeNodeChunk
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallTree
import CFSG.Certificates.Kernel.Common.Harness

public section

#kc_repo #kc_items_root CFSG.KC.J4TreeN.Data.c07f "Certificates/Kernel/J4TreeNode/data/c07.fld.items" 145382 6436466108779650519
#kc_repo #kc_items_root CFSG.KC.J4TreeN.Data.c07o "Certificates/Kernel/J4TreeNode/data/c07.off.items" 700 18364784580431741948

namespace CFSG.KC.J4TreeN

@[expose] noncomputable def rec07 (j : Nat) : NRec := parseRec (nodeFlds Data.c07f (Data.c07o j))

@[expose] noncomputable def chk07 (j : Nat) : Bool := chunkNodeOK tabs 7 rec07 j

set_option maxRecDepth 400000

#kc_each chk07 0 100

#kc_forall_tree chk07_all (fun j => chk07 j = true) 100 CFSG.KC.J4TreeN.chk07

@[expose] noncomputable def edgeN07 (j : Nat) : Bool := edgeNodeChk 7 rec07 j

#kc_each edgeN07 0 100

#kc_forall_tree edgeN07_all (fun j => edgeN07 j = true) 100 CFSG.KC.J4TreeN.edgeN07

theorem edge07 : edgeChk 7 rec07 = true := edgeChk_of_nodes edgeN07_all

end CFSG.KC.J4TreeN
