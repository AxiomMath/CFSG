module

public import Certificates.Kernel.J4TreeTop.Walk134
public import Certificates.Data.Kernel.J4TreeTopCoverK
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallTree
import CFSG.Certificates.Kernel.Common.Harness

public section

#kc_repo #kc_items_root CFSG.KC.J4TreeT.Data.cv134 "Certificates/Kernel/J4TreeTop/data/cover134.items" 11698 13947702725404722728

namespace CFSG.KC.J4TreeT

open CFSG.KC.J4TreeN CFSG.J4Tree.Native

@[expose] noncomputable def cv134G : CKGlob := parseCK 3 (decF 4096 (Data.cv134 1024))

@[expose] noncomputable def cv134Rec (e : Nat) : List Nat := decF 16384 (Data.cv134 e)

@[expose] noncomputable def cvChk134 (e : Nat) : Bool :=
  coverKOK tabs wB134 hd134 cv134G e (decF 4096 (Data.w134 e)) (cv134Rec e)

set_option maxRecDepth 400000

theorem cv134_glob : ckGlobOK tabs wB134 hd134 topNode134 cv134G = true := by quickRfl

#kc_each cvChk134 0 1024

#kc_forall_tree cv134_all (fun e => cvChk134 e = true) 1024 CFSG.KC.J4TreeT.cvChk134

end CFSG.KC.J4TreeT
