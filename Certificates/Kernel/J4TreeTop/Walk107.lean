module

public import Certificates.Kernel.J4TreeNode.Tabs
public import Certificates.Data.Kernel.J4TreeTopWalk
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallTree
import CFSG.Certificates.Kernel.Common.Harness

public section

#kc_repo #kc_items_root CFSG.KC.J4TreeT.Data.w107 "Certificates/Kernel/J4TreeTop/data/walk107.items" 9663 4536715509559597071

namespace CFSG.KC.J4TreeT

open CFSG.KC.J4TreeN CFSG.J4Tree.Native

@[expose] def wC107 : List (Nat × Nat) := [(1131, 0), (952, 66), (1352, 586)]

theorem wC107_eq : treeBasis 107 = wC107 := by decide +kernel

@[expose] noncomputable def wB107 : List Nat := wC107.map (ccT tabs)

@[expose] noncomputable def hd107 : WHd := parseWHd (decF 4096 (Data.w107 1024))

@[expose] noncomputable def wChk107 (e : Nat) : Bool :=
  walkOK tabs wB107 hd107 e (decF 4096 (Data.w107 e))

set_option maxRecDepth 400000

theorem hd107_ok : whdOK tabs wB107 hd107 = true := by quickRfl

#kc_each wChk107 0 1024

#kc_forall_tree w107_all (fun e => wChk107 e = true) 1024 CFSG.KC.J4TreeT.wChk107

end CFSG.KC.J4TreeT
