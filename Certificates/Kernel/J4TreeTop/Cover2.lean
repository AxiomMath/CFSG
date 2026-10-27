module

public import Certificates.Kernel.J4TreeTop.Walk2
public import Certificates.Data.Kernel.J4TreeTopCoverK
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallTree
import CFSG.Certificates.Kernel.Common.Harness

public section

#kc_repo #kc_items_root CFSG.KC.J4TreeT.Data.cv2 "Certificates/Kernel/J4TreeTop/data/cover2.items" 12454 9069184289222800697

namespace CFSG.KC.J4TreeT

open CFSG.KC.J4TreeN CFSG.J4Tree.Native

@[expose] noncomputable def cv2G : CKGlob := parseCK 2 (decF 4096 (Data.cv2 1024))

@[expose] noncomputable def cv2Rec (e : Nat) : List Nat := decF 16384 (Data.cv2 e)

@[expose] noncomputable def cvChk2 (e : Nat) : Bool :=
  coverKOK tabs wB2 hd2 cv2G e (decF 4096 (Data.w2 e)) (cv2Rec e)

set_option maxRecDepth 400000

theorem cv2_glob : ckGlobOK tabs wB2 hd2 topNode2 cv2G = true := by quickRfl

#kc_each cvChk2 0 1024

#kc_forall_tree cv2_all (fun e => cvChk2 e = true) 1024 CFSG.KC.J4TreeT.cvChk2

end CFSG.KC.J4TreeT
