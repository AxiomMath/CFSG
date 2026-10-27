module

public import Certificates.Kernel.J4TreeNode.Tabs
public import Certificates.Data.Kernel.J4TreeTopWalk
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallTree
import CFSG.Certificates.Kernel.Common.Harness

public section

#kc_repo #kc_items_root CFSG.KC.J4TreeT.Data.w134 "Certificates/Kernel/J4TreeTop/data/walk134.items" 10671 16564127014312879951

namespace CFSG.KC.J4TreeT

open CFSG.KC.J4TreeN CFSG.J4Tree.Native

@[expose] def wC134 : List (Nat × Nat) := [(422, 0), (911, 0), (1485, 0)]

theorem wC134_eq : treeBasis 134 = wC134 := by decide +kernel

@[expose] noncomputable def wB134 : List Nat := wC134.map (ccT tabs)

@[expose] noncomputable def hd134 : WHd := parseWHd (decF 4096 (Data.w134 1024))

@[expose] noncomputable def wChk134 (e : Nat) : Bool :=
  walkOK tabs wB134 hd134 e (decF 4096 (Data.w134 e))

set_option maxRecDepth 400000

theorem hd134_ok : whdOK tabs wB134 hd134 = true := by quickRfl

#kc_each wChk134 0 1024

#kc_forall_tree w134_all (fun e => wChk134 e = true) 1024 CFSG.KC.J4TreeT.wChk134

end CFSG.KC.J4TreeT
