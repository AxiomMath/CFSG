module

public import Certificates.Kernel.J4TreeNode.Tabs
public import Certificates.Data.Kernel.J4TreeTopWalk
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallTree
import CFSG.Certificates.Kernel.Common.Harness

public section

#kc_repo #kc_items_root CFSG.KC.J4TreeT.Data.w129 "Certificates/Kernel/J4TreeTop/data/walk129.items" 9745 4570730793250359741

namespace CFSG.KC.J4TreeT

open CFSG.KC.J4TreeN CFSG.J4Tree.Native

@[expose] def wC129 : List (Nat × Nat) := [(1131, 0), (1079, 984), (383, 984)]

theorem wC129_eq : treeBasis 129 = wC129 := by decide +kernel

@[expose] noncomputable def wB129 : List Nat := wC129.map (ccT tabs)

@[expose] noncomputable def hd129 : WHd := parseWHd (decF 4096 (Data.w129 1024))

@[expose] noncomputable def wChk129 (e : Nat) : Bool :=
  walkOK tabs wB129 hd129 e (decF 4096 (Data.w129 e))

set_option maxRecDepth 400000

theorem hd129_ok : whdOK tabs wB129 hd129 = true := by quickRfl

#kc_each wChk129 0 1024

#kc_forall_tree w129_all (fun e => wChk129 e = true) 1024 CFSG.KC.J4TreeT.wChk129

end CFSG.KC.J4TreeT
