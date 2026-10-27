module

public import Certificates.Kernel.J4TreeTop.Sylow
public import Certificates.Data.Kernel.J4TreeTopUneq
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallTree

public section

#kc_repo #kc_items_root CFSG.KC.J4TreeS.Data.un "Certificates/Kernel/J4TreeTop/data/uneq.items" 238457 14174783076265166255

namespace CFSG.KC.J4TreeS

open CFSG.KC.J4TreeN

@[expose] noncomputable def unRec (t : Nat) : TUneq := parseU (decF 4096 (Data.un (2 * t)))

@[expose] noncomputable def unEnts (t : Nat) : List (Nat × Nat × Nat) :=
  (decW 160 32 (unRec t).L (Data.un (2 * t + 1))).map entOf

@[expose] noncomputable def unChk (t : Nat) : Bool :=
  if (unRec t).tgt = 0 then topPruneOK tabs (syRec (unRec t).i) (unRec t) (unEnts t)
  else topUneqOK tabs (syRec (unRec t).i) (unRec t) (unEnts t)

set_option maxRecDepth 400000

#kc_each unChk 0 16

#kc_forall_tree un_all (fun t => unChk t = true) 16 CFSG.KC.J4TreeS.unChk

end CFSG.KC.J4TreeS
