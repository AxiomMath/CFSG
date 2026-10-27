module

public import Certificates.Kernel.J4TreeNode.Tabs
public import Certificates.Data.Kernel.J4TreeNodeChunk
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallTree
import CFSG.Certificates.Kernel.Common.Harness

public section

#kc_repo #kc_items_root CFSG.KC.J4TreeN.Data.c00 "Certificates/Kernel/J4TreeNode/data/c00.items" 527201 5426331095335526432

namespace CFSG.KC.J4TreeN

@[expose] noncomputable def rec00 (j : Nat) : NRec := parseRec (decF 1048576 (Data.c00 j))

@[expose] noncomputable def chk00 (j : Nat) : Bool := chunkNodeOK tabs 0 rec00 j

set_option maxRecDepth 400000

#kc_each chk00 0 100

#kc_forall_tree chk00_all (fun j => chk00 j = true) 100 CFSG.KC.J4TreeN.chk00

theorem edge00 : edgeChk 0 rec00 = true := by quickRfl

end CFSG.KC.J4TreeN
