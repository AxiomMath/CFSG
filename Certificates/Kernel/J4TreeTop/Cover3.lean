module

public import Certificates.Kernel.J4TreeTop.Walk3
public import Certificates.Data.Kernel.J4TreeTopCoverK
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallTree
import CFSG.Certificates.Kernel.Common.Harness

public section

#kc_repo #kc_items_root CFSG.KC.J4TreeT.Data.cv3 "Certificates/Kernel/J4TreeTop/data/cover3.items" 11498 17152143164608432126

namespace CFSG.KC.J4TreeT

open CFSG.KC.J4TreeN CFSG.J4Tree.Native

@[expose] noncomputable def cv3G : CKGlob := parseCK 2 (decF 4096 (Data.cv3 1024))

@[expose] noncomputable def cv3Rec (e : Nat) : List Nat := decF 16384 (Data.cv3 e)

@[expose] noncomputable def cvChk3 (e : Nat) : Bool :=
  coverKOK tabs wB3 hd3 cv3G e (decF 4096 (Data.w3 e)) (cv3Rec e)

set_option maxRecDepth 400000

theorem cv3_glob : ckGlobOK tabs wB3 hd3 topNode3 cv3G = true := by quickRfl

#kc_each cvChk3 0 1024

#kc_forall_tree cv3_all (fun e => cvChk3 e = true) 1024 CFSG.KC.J4TreeT.cvChk3

end CFSG.KC.J4TreeT
