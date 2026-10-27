module

public import Certificates.Kernel.J4TreeNode.Tabs
public import Certificates.Data.Kernel.J4TreeTopWalk
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallTree
import CFSG.Certificates.Kernel.Common.Harness

public section

#kc_repo #kc_items_root CFSG.KC.J4TreeT.Data.w3 "Certificates/Kernel/J4TreeTop/data/walk3.items" 15445 18002883285961667501

namespace CFSG.KC.J4TreeT

open CFSG.KC.J4TreeN CFSG.J4Tree.Native

@[expose] def wC3 : List (Nat × Nat) := [(1131, 0), (1131, 72)]

theorem wC3_eq : treeBasis 3 = wC3 := by decide +kernel

@[expose] noncomputable def wB3 : List Nat := wC3.map (ccT tabs)

@[expose] noncomputable def hd3 : WHd := parseWHd (decF 4096 (Data.w3 1024))

@[expose] noncomputable def wChk3 (e : Nat) : Bool := walkOK tabs wB3 hd3 e (decF 4096 (Data.w3 e))

set_option maxRecDepth 400000

theorem hd3_ok : whdOK tabs wB3 hd3 = true := by quickRfl

#kc_each wChk3 0 1024

#kc_forall_tree w3_all (fun e => wChk3 e = true) 1024 CFSG.KC.J4TreeT.wChk3

end CFSG.KC.J4TreeT
