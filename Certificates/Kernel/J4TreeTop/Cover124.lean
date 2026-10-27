module

public import Certificates.Kernel.J4TreeTop.Walk124
public import Certificates.Data.Kernel.J4TreeTopCoverK
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallTree
import CFSG.Certificates.Kernel.Common.Harness

public section

#kc_repo #kc_items_root CFSG.KC.J4TreeT.Data.cv124 "Certificates/Kernel/J4TreeTop/data/cover124.items" 8525 3897522058396853437

namespace CFSG.KC.J4TreeT

open CFSG.KC.J4TreeN CFSG.J4Tree.Native

@[expose] noncomputable def cv124G : CKGlob := parseCK 3 (decF 4096 (Data.cv124 1024))

@[expose] noncomputable def cv124Rec (e : Nat) : List Nat := decF 16384 (Data.cv124 e)

@[expose] noncomputable def cvChk124 (e : Nat) : Bool :=
  coverKOK tabs wB124 hd124 cv124G e (decF 4096 (Data.w124 e)) (cv124Rec e)

set_option maxRecDepth 400000

theorem cv124_glob : ckGlobOK tabs wB124 hd124 topNode124 cv124G = true := by quickRfl

#kc_each cvChk124 0 1024

#kc_forall_tree cv124_all (fun e => cvChk124 e = true) 1024 CFSG.KC.J4TreeT.cvChk124

end CFSG.KC.J4TreeT
