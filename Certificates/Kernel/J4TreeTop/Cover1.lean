module

public import Certificates.Kernel.J4TreeTop.ECut
public import Certificates.Data.Kernel.J4TreeTopCover
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallTree
import CFSG.Certificates.Kernel.Common.Harness

public section

#kc_repo #kc_items_root CFSG.KC.J4TreeT.Data.c1 "Certificates/Kernel/J4TreeTop/data/cover1.items" 23828 4151859540665356126

namespace CFSG.KC.J4TreeT

open CFSG.KC.J4TreeN

@[expose] noncomputable def c1G : C1Glob := parseC1 (decF 4096 (Data.c1 1024))

@[expose] noncomputable def c1Rec (e : Nat) : List Nat := decF 16384 (Data.c1 e)

@[expose] noncomputable def c1Chk (e : Nat) : Bool := cover1OK tabs 1131 e c1G (ecRec e) (c1Rec e)

set_option maxRecDepth 400000

theorem c1_glob : c1GlobOK tabs 1131 c1G = true := by quickRfl

#kc_each c1Chk 0 1024

#kc_forall_tree c1_all (fun e => c1Chk e = true) 1024 CFSG.KC.J4TreeT.c1Chk

end CFSG.KC.J4TreeT
