module

public import Certificates.Kernel.J4TreeNode.Tabs
public import Certificates.Data.Kernel.J4TreeNodeChunk
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallTree
import CFSG.Certificates.Kernel.Common.Harness

public section

#kc_repo #kc_items_root CFSG.KC.J4TreeN.Data.c08 "Certificates/Kernel/J4TreeNode/data/c08.items" 153725 2135561875347765663

namespace CFSG.KC.J4TreeN

@[expose] noncomputable def rec08 (j : Nat) : NRec := parseRec (decF 1048576 (Data.c08 j))

@[expose] noncomputable def chk08 (j : Nat) : Bool := chunkNodeOK tabs 8 rec08 j

set_option maxRecDepth 400000

#kc_each chk08 0 100

#kc_forall_tree chk08_all (fun j => chk08 j = true) 100 CFSG.KC.J4TreeN.chk08

theorem edge08 : edgeChk 8 rec08 = true := by quickRfl

end CFSG.KC.J4TreeN
