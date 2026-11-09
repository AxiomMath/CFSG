module

public import Certificates.Kernel.J4TreeNode.Tabs
public import Certificates.Data.Kernel.J4TreeNodeChunk
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallTree
import CFSG.Certificates.Kernel.Common.Harness

public section

#kc_repo #kc_items_root CFSG.KC.J4TreeN.Data.c06f "Certificates/Kernel/J4TreeNode/data/c06.fld.items" 158899 15533984438658848956
#kc_repo #kc_items_root CFSG.KC.J4TreeN.Data.c06o "Certificates/Kernel/J4TreeNode/data/c06.off.items" 700 6085213209732937664

namespace CFSG.KC.J4TreeN

@[expose] noncomputable def rec06 (j : Nat) : NRec := parseRec (nodeFlds Data.c06f (Data.c06o j))

@[expose] noncomputable def chk06 (j : Nat) : Bool := chunkNodeOK tabs 6 rec06 j

set_option maxRecDepth 400000

#kc_each chk06 0 100

#kc_forall_tree chk06_all (fun j => chk06 j = true) 100 CFSG.KC.J4TreeN.chk06

@[expose] noncomputable def edgeN06 (j : Nat) : Bool := edgeNodeChk 6 rec06 j

#kc_each edgeN06 0 100

#kc_forall_tree edgeN06_all (fun j => edgeN06 j = true) 100 CFSG.KC.J4TreeN.edgeN06

theorem edge06 : edgeChk 6 rec06 = true := edgeChk_of_nodes edgeN06_all

end CFSG.KC.J4TreeN
