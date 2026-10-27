module

public import Certificates.Kernel.J4TreeNode.Tabs
public import Certificates.Data.Kernel.J4TreeNodeChunk
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallTree
import CFSG.Certificates.Kernel.Common.Harness

public section

#kc_repo #kc_items_root CFSG.KC.J4TreeN.Data.c03 "Certificates/Kernel/J4TreeNode/data/c03.items" 251769 4394005039151072240

namespace CFSG.KC.J4TreeN

@[expose] noncomputable def rec03 (j : Nat) : NRec := parseRec (decF 1048576 (Data.c03 j))

@[expose] noncomputable def chk03 (j : Nat) : Bool := chunkNodeOK tabs 3 rec03 j

set_option maxRecDepth 400000

#kc_each chk03 0 100

#kc_forall_tree chk03_all (fun j => chk03 j = true) 100 CFSG.KC.J4TreeN.chk03

theorem edge03 : edgeChk 3 rec03 = true := by quickRfl

end CFSG.KC.J4TreeN
