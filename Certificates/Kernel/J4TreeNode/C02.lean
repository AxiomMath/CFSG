module

public import Certificates.Kernel.J4TreeNode.Tabs
public import Certificates.Data.Kernel.J4TreeNodeChunk
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallTree
import CFSG.Certificates.Kernel.Common.Harness

public section

#kc_repo #kc_items_root CFSG.KC.J4TreeN.Data.c02f "Certificates/Kernel/J4TreeNode/data/c02.fld.items" 248210 11552894429183132541
#kc_repo #kc_items_root CFSG.KC.J4TreeN.Data.c02o "Certificates/Kernel/J4TreeNode/data/c02.off.items" 727 10135878251892703364

namespace CFSG.KC.J4TreeN

@[expose] noncomputable def rec02 (j : Nat) : NRec := parseRec (nodeFlds Data.c02f (Data.c02o j))

@[expose] noncomputable def chk02 (j : Nat) : Bool := chunkNodeOK tabs 2 rec02 j

set_option maxRecDepth 400000

#kc_each chk02 0 100

#kc_forall_tree chk02_all (fun j => chk02 j = true) 100 CFSG.KC.J4TreeN.chk02

@[expose] noncomputable def edgeN02 (j : Nat) : Bool := edgeNodeChk 2 rec02 j

#kc_each edgeN02 0 100

#kc_forall_tree edgeN02_all (fun j => edgeN02 j = true) 100 CFSG.KC.J4TreeN.edgeN02

theorem edge02 : edgeChk 2 rec02 = true := edgeChk_of_nodes edgeN02_all

end CFSG.KC.J4TreeN
