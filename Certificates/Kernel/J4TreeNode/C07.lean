module

public import Certificates.Kernel.J4TreeNode.Tabs
public import Certificates.Data.Kernel.J4TreeNodeChunk
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallTree
import CFSG.Certificates.Kernel.Common.Harness

public section

#kc_repo #kc_items_root CFSG.KC.J4TreeN.Data.c07 "Certificates/Kernel/J4TreeNode/data/c07.items" 142270 8203292041618356796

namespace CFSG.KC.J4TreeN

@[expose] noncomputable def rec07 (j : Nat) : NRec := parseRec (decF 1048576 (Data.c07 j))

@[expose] noncomputable def chk07 (j : Nat) : Bool := chunkNodeOK tabs 7 rec07 j

set_option maxRecDepth 400000

#kc_each chk07 0 100

#kc_forall_tree chk07_all (fun j => chk07 j = true) 100 CFSG.KC.J4TreeN.chk07

theorem edge07 : edgeChk 7 rec07 = true := by quickRfl

end CFSG.KC.J4TreeN
