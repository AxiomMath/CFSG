module

public import Certificates.Kernel.J4TreeNode.Tabs
public import Certificates.Data.Kernel.J4TreeTopWalk
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallTree
import CFSG.Certificates.Kernel.Common.Harness

public section

#kc_repo #kc_items_root CFSG.KC.J4TreeT.Data.w124 "Certificates/Kernel/J4TreeTop/data/walk124.items" 12167 2555273222434589541

namespace CFSG.KC.J4TreeT

open CFSG.KC.J4TreeN CFSG.J4Tree.Native

@[expose] def wC124 : List (Nat × Nat) := [(1131, 0), (209, 464), (1898, 576)]

theorem wC124_eq : treeBasis 124 = wC124 := by decide +kernel

@[expose] noncomputable def wB124 : List Nat := wC124.map (ccT tabs)

@[expose] noncomputable def hd124 : WHd := parseWHd (decF 4096 (Data.w124 1024))

@[expose] noncomputable def wChk124 (e : Nat) : Bool :=
  walkOK tabs wB124 hd124 e (decF 4096 (Data.w124 e))

set_option maxRecDepth 400000

theorem hd124_ok : whdOK tabs wB124 hd124 = true := by quickRfl

#kc_each wChk124 0 1024

#kc_forall_tree w124_all (fun e => wChk124 e = true) 1024 CFSG.KC.J4TreeT.wChk124

end CFSG.KC.J4TreeT
