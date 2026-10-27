module

public import Certificates.Kernel.J4TreeNode.Tabs
public import Certificates.Data.Kernel.J4TreeTopWalk
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallTree
import CFSG.Certificates.Kernel.Common.Harness

public section

#kc_repo #kc_items_root CFSG.KC.J4TreeT.Data.w4 "Certificates/Kernel/J4TreeTop/data/walk4.items" 22546 390943892310054156

namespace CFSG.KC.J4TreeT

open CFSG.KC.J4TreeN CFSG.J4Tree.Native

@[expose] def wC4 : List (Nat × Nat) := [(1131, 0), (2020, 0)]

theorem wC4_eq : treeBasis 4 = wC4 := by decide +kernel

@[expose] noncomputable def wB4 : List Nat := wC4.map (ccT tabs)

@[expose] noncomputable def hd4 : WHd := parseWHd (decF 4096 (Data.w4 1024))

@[expose] noncomputable def wChk4 (e : Nat) : Bool := walkOK tabs wB4 hd4 e (decF 4096 (Data.w4 e))

set_option maxRecDepth 400000

theorem hd4_ok : whdOK tabs wB4 hd4 = true := by quickRfl

#kc_each wChk4 0 1024

#kc_forall_tree w4_all (fun e => wChk4 e = true) 1024 CFSG.KC.J4TreeT.wChk4

end CFSG.KC.J4TreeT
