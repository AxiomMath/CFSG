module

public import Certificates.Kernel.J4TreeTop.Walk107
public import Certificates.Data.Kernel.J4TreeTopCoverK
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallTree
import CFSG.Certificates.Kernel.Common.Harness

public section

#kc_repo #kc_items_root CFSG.KC.J4TreeT.Data.cv107 "Certificates/Kernel/J4TreeTop/data/cover107.items" 7330 17762435806006002629

namespace CFSG.KC.J4TreeT

open CFSG.KC.J4TreeN CFSG.J4Tree.Native

@[expose] noncomputable def cv107G : CKGlob := parseCK 3 (decF 4096 (Data.cv107 1024))

@[expose] noncomputable def cv107Rec (e : Nat) : List Nat := decF 16384 (Data.cv107 e)

@[expose] noncomputable def cvChk107 (e : Nat) : Bool :=
  coverKOK tabs wB107 hd107 cv107G e (decF 4096 (Data.w107 e)) (cv107Rec e)

set_option maxRecDepth 400000

theorem cv107_glob : ckGlobOK tabs wB107 hd107 topNode107 cv107G = true := by quickRfl

#kc_each cvChk107 0 1024

#kc_forall_tree cv107_all (fun e => cvChk107 e = true) 1024 CFSG.KC.J4TreeT.cvChk107

end CFSG.KC.J4TreeT
