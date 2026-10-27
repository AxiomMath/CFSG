module

public import Certificates.Kernel.J4TreeTop.Walk4
public import Certificates.Data.Kernel.J4TreeTopCoverK
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallTree
import CFSG.Certificates.Kernel.Common.Harness

public section

#kc_repo #kc_items_root CFSG.KC.J4TreeT.Data.cv4 "Certificates/Kernel/J4TreeTop/data/cover4.items" 16150 13821362453575596467

namespace CFSG.KC.J4TreeT

open CFSG.KC.J4TreeN CFSG.J4Tree.Native

@[expose] noncomputable def cv4G : CKGlob := parseCK 2 (decF 4096 (Data.cv4 1024))

@[expose] noncomputable def cv4Rec (e : Nat) : List Nat := decF 16384 (Data.cv4 e)

@[expose] noncomputable def cvChk4 (e : Nat) : Bool :=
  coverKOK tabs wB4 hd4 cv4G e (decF 4096 (Data.w4 e)) (cv4Rec e)

set_option maxRecDepth 400000

theorem cv4_glob : ckGlobOK tabs wB4 hd4 topNode4 cv4G = true := by quickRfl

#kc_each cvChk4 0 1024

#kc_forall_tree cv4_all (fun e => cvChk4 e = true) 1024 CFSG.KC.J4TreeT.cvChk4

end CFSG.KC.J4TreeT
