module

public import Certificates.Kernel.J4TreeTop.Walk7
public import Certificates.Data.Kernel.J4TreeTopCoverK
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallTree
import CFSG.Certificates.Kernel.Common.Harness

public section

#kc_repo #kc_items_root CFSG.KC.J4TreeT.Data.cv7 "Certificates/Kernel/J4TreeTop/data/cover7.items" 7148 4973820860779226540

namespace CFSG.KC.J4TreeT

open CFSG.KC.J4TreeN CFSG.J4Tree.Native

@[expose] noncomputable def cv7G : CKGlob := parseCK 3 (decF 4096 (Data.cv7 1024))

@[expose] noncomputable def cv7Rec (e : Nat) : List Nat := decF 16384 (Data.cv7 e)

@[expose] noncomputable def cvChk7 (e : Nat) : Bool :=
  coverKOK tabs wB7 hd7 cv7G e (decF 4096 (Data.w7 e)) (cv7Rec e)

set_option maxRecDepth 400000

theorem cv7_glob : ckGlobOK tabs wB7 hd7 topNode7 cv7G = true := by quickRfl

#kc_each cvChk7 0 1024

#kc_forall_tree cv7_all (fun e => cvChk7 e = true) 1024 CFSG.KC.J4TreeT.cvChk7

end CFSG.KC.J4TreeT
