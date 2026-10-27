module

public import Certificates.Kernel.J4TreeNode.Tabs
public import Certificates.Data.Kernel.J4TreeTopWalk
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallTree
import CFSG.Certificates.Kernel.Common.Harness

public section

#kc_repo #kc_items_root CFSG.KC.J4TreeT.Data.w2 "Certificates/Kernel/J4TreeTop/data/walk2.items" 23922 11824265290616125493

namespace CFSG.KC.J4TreeT

open CFSG.KC.J4TreeN CFSG.J4Tree.Native

@[expose] def wC2 : List (Nat × Nat) := [(451, 576), (1448, 576)]

theorem wC2_eq : treeBasis 2 = wC2 := by decide +kernel

@[expose] noncomputable def wB2 : List Nat := wC2.map (ccT tabs)

@[expose] noncomputable def hd2 : WHd := parseWHd (decF 4096 (Data.w2 1024))

@[expose] noncomputable def wChk2 (e : Nat) : Bool := walkOK tabs wB2 hd2 e (decF 4096 (Data.w2 e))

set_option maxRecDepth 400000

theorem hd2_ok : whdOK tabs wB2 hd2 = true := by quickRfl

#kc_each wChk2 0 1024

#kc_forall_tree w2_all (fun e => wChk2 e = true) 1024 CFSG.KC.J4TreeT.wChk2

end CFSG.KC.J4TreeT
