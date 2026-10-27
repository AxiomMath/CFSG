module

public import Certificates.Kernel.J4TreeNode.Tabs
public import Certificates.Data.Kernel.J4TreeNodeChunk
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallTree
import CFSG.Certificates.Kernel.Common.Harness

public section

#kc_repo #kc_items_root CFSG.KC.J4TreeN.Data.c02 "Certificates/Kernel/J4TreeNode/data/c02.items" 242170 3665375190391944424

namespace CFSG.KC.J4TreeN

@[expose] noncomputable def rec02 (j : Nat) : NRec := parseRec (decF 1048576 (Data.c02 j))

@[expose] noncomputable def chk02 (j : Nat) : Bool := chunkNodeOK tabs 2 rec02 j

set_option maxRecDepth 400000

#kc_each chk02 0 100

#kc_forall_tree chk02_all (fun j => chk02 j = true) 100 CFSG.KC.J4TreeN.chk02

theorem edge02 : edgeChk 2 rec02 = true := by quickRfl

end CFSG.KC.J4TreeN
