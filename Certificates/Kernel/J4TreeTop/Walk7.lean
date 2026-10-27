module

public import Certificates.Kernel.J4TreeNode.Tabs
public import Certificates.Data.Kernel.J4TreeTopWalk
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallTree
import CFSG.Certificates.Kernel.Common.Harness

public section

#kc_repo #kc_items_root CFSG.KC.J4TreeT.Data.w7 "Certificates/Kernel/J4TreeTop/data/walk7.items" 9743 16777954465127392316

namespace CFSG.KC.J4TreeT

open CFSG.KC.J4TreeN CFSG.J4Tree.Native

@[expose] def wC7 : List (Nat × Nat) := [(1131, 0), (778, 72), (911, 72)]

theorem wC7_eq : treeBasis 7 = wC7 := by decide +kernel

@[expose] noncomputable def wB7 : List Nat := wC7.map (ccT tabs)

@[expose] noncomputable def hd7 : WHd := parseWHd (decF 4096 (Data.w7 1024))

@[expose] noncomputable def wChk7 (e : Nat) : Bool := walkOK tabs wB7 hd7 e (decF 4096 (Data.w7 e))

set_option maxRecDepth 400000

theorem hd7_ok : whdOK tabs wB7 hd7 = true := by quickRfl

#kc_each wChk7 0 1024

#kc_forall_tree w7_all (fun e => wChk7 e = true) 1024 CFSG.KC.J4TreeT.wChk7

end CFSG.KC.J4TreeT
