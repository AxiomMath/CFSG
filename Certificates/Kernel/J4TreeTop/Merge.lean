module

public import Certificates.Kernel.J4TreeTop.Sylow
public import Certificates.Data.Kernel.J4TreeTopMerge
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallTree

public section

#kc_repo #kc_items_root CFSG.KC.J4TreeS.Data.mg "Certificates/Kernel/J4TreeTop/data/merge.items" 825338 13249087891598131977

namespace CFSG.KC.J4TreeS

open CFSG.KC.J4TreeN

@[expose] noncomputable def mgRec (t : Nat) : TMerge := parseM (decF 64 (Data.mg (2 * t)))

@[expose] noncomputable def mgEnts (t : Nat) : List (Nat × Nat × Nat) :=
  (decW 160 32 (mgRec t).L (Data.mg (2 * t + 1))).map entOf

@[expose] noncomputable def mgChk (t : Nat) : Bool :=
  topMergeOK tabs (syRec (mgRec t).i) (mgRec t) (mgEnts t)

set_option maxRecDepth 400000

#kc_each mgChk 0 152

#kc_forall_tree mg_all (fun t => mgChk t = true) 152 CFSG.KC.J4TreeS.mgChk

end CFSG.KC.J4TreeS
