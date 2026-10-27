module

public import Certificates.Kernel.J4TreeNode.Tabs
public import Certificates.Data.Kernel.J4TreeNodeChunk
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallTree
import CFSG.Certificates.Kernel.Common.Harness

public section

#kc_repo #kc_items_root CFSG.KC.J4TreeN.Data.c05 "Certificates/Kernel/J4TreeNode/data/c05.items" 191892 3346437369809684743

namespace CFSG.KC.J4TreeN

@[expose] noncomputable def rec05 (j : Nat) : NRec := parseRec (decF 1048576 (Data.c05 j))

@[expose] noncomputable def chk05 (j : Nat) : Bool := chunkNodeOK tabs 5 rec05 j

set_option maxRecDepth 400000

#kc_each chk05 0 100

#kc_forall_tree chk05_all (fun j => chk05 j = true) 100 CFSG.KC.J4TreeN.chk05

theorem edge05 : edgeChk 5 rec05 = true := by quickRfl

end CFSG.KC.J4TreeN
