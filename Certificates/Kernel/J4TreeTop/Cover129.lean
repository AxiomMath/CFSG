module

public import Certificates.Kernel.J4TreeTop.Walk129
public import Certificates.Data.Kernel.J4TreeTopCoverK
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallTree
import CFSG.Certificates.Kernel.Common.Harness

public section

#kc_repo #kc_items_root CFSG.KC.J4TreeT.Data.cv129 "Certificates/Kernel/J4TreeTop/data/cover129.items" 6803 15281900389709247214

namespace CFSG.KC.J4TreeT

open CFSG.KC.J4TreeN CFSG.J4Tree.Native

@[expose] noncomputable def cv129G : CKGlob := parseCK 3 (decF 4096 (Data.cv129 1024))

@[expose] noncomputable def cv129Rec (e : Nat) : List Nat := decF 16384 (Data.cv129 e)

@[expose] noncomputable def cvChk129 (e : Nat) : Bool :=
  coverKOK tabs wB129 hd129 cv129G e (decF 4096 (Data.w129 e)) (cv129Rec e)

set_option maxRecDepth 400000

theorem cv129_glob : ckGlobOK tabs wB129 hd129 topNode129 cv129G = true := by quickRfl

#kc_each cvChk129 0 1024

#kc_forall_tree cv129_all (fun e => cvChk129 e = true) 1024 CFSG.KC.J4TreeT.cvChk129

end CFSG.KC.J4TreeT
