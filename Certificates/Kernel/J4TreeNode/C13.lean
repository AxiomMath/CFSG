module

public import Certificates.Kernel.J4TreeNode.Tabs
public import Certificates.Data.Kernel.J4TreeNodeChunk
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallTree
import CFSG.Certificates.Kernel.Common.Harness

public section

#kc_repo #kc_items_root CFSG.KC.J4TreeN.Data.c13 "Certificates/Kernel/J4TreeNode/data/c13.items" 15302 7452779170759270620

namespace CFSG.KC.J4TreeN

@[expose] noncomputable def rec13 (j : Nat) : NRec := parseRec (decF 1048576 (Data.c13 j))

@[expose] noncomputable def chk13 (j : Nat) : Bool := chunkNodeOK tabs 13 rec13 j

set_option maxRecDepth 400000

#kc_each chk13 0 100

#kc_forall_tree chk13_all (fun j => chk13 j = true) 100 CFSG.KC.J4TreeN.chk13

theorem edge13 : edgeChk 13 rec13 = true := by quickRfl

end CFSG.KC.J4TreeN
