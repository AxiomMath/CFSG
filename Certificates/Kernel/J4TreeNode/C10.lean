module

public import Certificates.Kernel.J4TreeNode.Tabs
public import Certificates.Data.Kernel.J4TreeNodeChunk
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallTree
import CFSG.Certificates.Kernel.Common.Harness

public section

#kc_repo #kc_items_root CFSG.KC.J4TreeN.Data.c10 "Certificates/Kernel/J4TreeNode/data/c10.items" 135918 9055634458962647252

namespace CFSG.KC.J4TreeN

@[expose] noncomputable def rec10 (j : Nat) : NRec := parseRec (decF 1048576 (Data.c10 j))

@[expose] noncomputable def chk10 (j : Nat) : Bool := chunkNodeOK tabs 10 rec10 j

set_option maxRecDepth 400000

#kc_each chk10 0 100

#kc_forall_tree chk10_all (fun j => chk10 j = true) 100 CFSG.KC.J4TreeN.chk10

theorem edge10 : edgeChk 10 rec10 = true := by quickRfl

end CFSG.KC.J4TreeN
