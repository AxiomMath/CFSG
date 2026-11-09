module

public import Certificates.Kernel.J4TreeNode.Tabs
public import Certificates.Data.Kernel.J4TreeNodeChunk
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallTree
import CFSG.Certificates.Kernel.Common.Harness

public section

#kc_repo #kc_items_root CFSG.KC.J4TreeN.Data.c08f "Certificates/Kernel/J4TreeNode/data/c08.fld.items" 157161 15453311358190713077
#kc_repo #kc_items_root CFSG.KC.J4TreeN.Data.c08o "Certificates/Kernel/J4TreeNode/data/c08.off.items" 701 13067904277369567929

namespace CFSG.KC.J4TreeN

@[expose] noncomputable def rec08 (j : Nat) : NRec := parseRec (nodeFlds Data.c08f (Data.c08o j))

@[expose] noncomputable def chk08 (j : Nat) : Bool := chunkNodeOK tabs 8 rec08 j

set_option maxRecDepth 400000

#kc_each chk08 0 100

#kc_forall_tree chk08_all (fun j => chk08 j = true) 100 CFSG.KC.J4TreeN.chk08

@[expose] noncomputable def edgeN08 (j : Nat) : Bool := edgeNodeChk 8 rec08 j

#kc_each edgeN08 0 100

#kc_forall_tree edgeN08_all (fun j => edgeN08 j = true) 100 CFSG.KC.J4TreeN.edgeN08

theorem edge08 : edgeChk 8 rec08 = true := edgeChk_of_nodes edgeN08_all

end CFSG.KC.J4TreeN
