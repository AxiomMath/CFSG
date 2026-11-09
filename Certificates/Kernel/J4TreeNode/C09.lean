module

public import Certificates.Kernel.J4TreeNode.Tabs
public import Certificates.Data.Kernel.J4TreeNodeChunk
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallTree
import CFSG.Certificates.Kernel.Common.Harness

public section

#kc_repo #kc_items_root CFSG.KC.J4TreeN.Data.c09f "Certificates/Kernel/J4TreeNode/data/c09.fld.items" 142067 9659439395235919335
#kc_repo #kc_items_root CFSG.KC.J4TreeN.Data.c09o "Certificates/Kernel/J4TreeNode/data/c09.off.items" 700 1285264840979289391

namespace CFSG.KC.J4TreeN

@[expose] noncomputable def rec09 (j : Nat) : NRec := parseRec (nodeFlds Data.c09f (Data.c09o j))

@[expose] noncomputable def chk09 (j : Nat) : Bool := chunkNodeOK tabs 9 rec09 j

set_option maxRecDepth 400000

#kc_each chk09 0 100

#kc_forall_tree chk09_all (fun j => chk09 j = true) 100 CFSG.KC.J4TreeN.chk09

@[expose] noncomputable def edgeN09 (j : Nat) : Bool := edgeNodeChk 9 rec09 j

#kc_each edgeN09 0 100

#kc_forall_tree edgeN09_all (fun j => edgeN09 j = true) 100 CFSG.KC.J4TreeN.edgeN09

theorem edge09 : edgeChk 9 rec09 = true := edgeChk_of_nodes edgeN09_all

end CFSG.KC.J4TreeN
