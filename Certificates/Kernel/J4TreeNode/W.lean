module

public import Certificates.Kernel.J4TreeNode.Tabs
public import Certificates.Data.Kernel.J4TreeNodeChunk
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallTree
import CFSG.Certificates.Kernel.Common.Harness

public section

#kc_repo #kc_items_root CFSG.KC.J4TreeN.Data.w "Certificates/Kernel/J4TreeNode/data/w.items" 108228 13071228822282172959

namespace CFSG.KC.J4TreeN

@[expose] noncomputable def recW (k : Nat) : WRec :=
  parseW (CFSG.J4Tree.Native.treeBasis k).length (decF 1048576 (Data.w k))

@[expose] noncomputable def chkW (k : Nat) : Bool := wAllOK tabs recW k

set_option maxRecDepth 400000

#kc_each chkW 0 1328

#kc_forall_tree chkW_all (fun k => chkW k = true) 1328 CFSG.KC.J4TreeN.chkW

theorem global_ok : CFSG.J4Tree.Native.Node.globalOK = true := by quickRfl

end CFSG.KC.J4TreeN
