module

public import Certificates.Kernel.J4TreeNode.Tabs
public import Certificates.Data.Kernel.J4TreeNodeChunk
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallTree
import CFSG.Certificates.Kernel.Common.Harness

public section

#kc_repo #kc_items_root CFSG.KC.J4TreeN.Data.c04 "Certificates/Kernel/J4TreeNode/data/c04.items" 209536 10440501273671528513

namespace CFSG.KC.J4TreeN

@[expose] noncomputable def rec04 (j : Nat) : NRec := parseRec (decF 1048576 (Data.c04 j))

@[expose] noncomputable def chk04 (j : Nat) : Bool := chunkNodeOK tabs 4 rec04 j

set_option maxRecDepth 400000

#kc_each chk04 0 100

#kc_forall_tree chk04_all (fun j => chk04 j = true) 100 CFSG.KC.J4TreeN.chk04

theorem edge04 : edgeChk 4 rec04 = true := by quickRfl

end CFSG.KC.J4TreeN
