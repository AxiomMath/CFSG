module

public import Certificates.Data.Kernel.Misc.PermInvCls
public import Certificates.Data.Kernel.LocalQT.Tc
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.HarnessGzTree
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_json_gz CertificateChecks.KernelU43T "Certificates/Kernel/U43Triple/data/u43t.json.gz"
  23182 15560416406340066678 (AL : List Nat) (DWL : List (List Nat)) (XWL : List (List Nat)) (XL : List Nat) (GWL : List (List Nat))
  (GL : List Nat) (PAL : List Nat) (SGL : List Nat) (CTL : List Nat) (RL : List Nat)
  (RWL : List (List Nat)) (CLL : List Nat)

#kc_repo #kc_ktree_gz CertificateChecks.KernelU43T E "Certificates/Kernel/U43Triple/data/u43tE.bin.gz"
  1025 4 131200 9463687761866642306

public section

namespace CertificateChecks.KernelU43T

open CFSG.KC.LQT.TC

@[expose] noncomputable def getW (L : List (List Nat)) (k : Nat) : List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => List.nil)
    (fun x _ ih k => Nat.rec (motive := fun _ => List Nat) x (fun j _ => ih j) k) L k

@[expose] noncomputable def A (i : Nat) : Nat := getTc 0 AL i
@[expose] noncomputable def DW (i : Nat) : List Nat := getW DWL i
@[expose] noncomputable def XW (i : Nat) : List Nat := getW XWL i
@[expose] noncomputable def X (i : Nat) : Nat := getTc 0 XL i
@[expose] noncomputable def GW (j : Nat) : List Nat := getW GWL j
@[expose] noncomputable def G (j : Nat) : Nat := getTc 0 GL j
@[expose] noncomputable def PA (k : Nat) : Nat := getTc 0 PAL k
@[expose] noncomputable def SG (i : Nat) : Nat := getTc 0 SGL i
@[expose] noncomputable def CT (i : Nat) : Nat := getTc 0 CTL i
@[expose] noncomputable def R (j : Nat) : Nat := getTc 0 RL j
@[expose] noncomputable def RW (j : Nat) : List Nat := getW RWL j
@[expose] noncomputable def CL (k : Nat) : Nat := getTc 0 CLL k

end CertificateChecks.KernelU43T

end
