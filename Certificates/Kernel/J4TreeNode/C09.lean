module

public import Certificates.Kernel.J4TreeNode.Tabs
public import Certificates.Data.Kernel.J4TreeNodeChunk
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallTree
import CFSG.Certificates.Kernel.Common.Harness

public section

#kc_repo #kc_items_root CFSG.KC.J4TreeN.Data.c09 "Certificates/Kernel/J4TreeNode/data/c09.items" 138959 8860215786313095184

namespace CFSG.KC.J4TreeN

@[expose] noncomputable def rec09 (j : Nat) : NRec := parseRec (decF 1048576 (Data.c09 j))

@[expose] noncomputable def chk09 (j : Nat) : Bool := chunkNodeOK tabs 9 rec09 j

set_option maxRecDepth 400000

#kc_each chk09 0 100

#kc_forall_tree chk09_all (fun j => chk09 j = true) 100 CFSG.KC.J4TreeN.chk09

theorem edge09 : edgeChk 9 rec09 = true := by quickRfl

end CFSG.KC.J4TreeN
