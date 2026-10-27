module

public import Certificates.Kernel.J4TreeNode.Tabs
public import Certificates.Data.Kernel.J4TreeNodeChunk
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallTree
import CFSG.Certificates.Kernel.Common.Harness

public section

#kc_repo #kc_items_root CFSG.KC.J4TreeN.Data.c06 "Certificates/Kernel/J4TreeNode/data/c06.items" 155527 3729879278093019367

namespace CFSG.KC.J4TreeN

@[expose] noncomputable def rec06 (j : Nat) : NRec := parseRec (decF 1048576 (Data.c06 j))

@[expose] noncomputable def chk06 (j : Nat) : Bool := chunkNodeOK tabs 6 rec06 j

set_option maxRecDepth 400000

#kc_each chk06 0 100

#kc_forall_tree chk06_all (fun j => chk06 j = true) 100 CFSG.KC.J4TreeN.chk06

theorem edge06 : edgeChk 6 rec06 = true := by quickRfl

end CFSG.KC.J4TreeN
