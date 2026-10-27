module

public import Certificates.Kernel.J4TreeCol.D7900
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallTree

public section

namespace CFSG.KC.J4TreeCol

@[expose] noncomputable def j4col7900_ (j : Nat) : Bool :=
  colNodeOK colMats CFSG.KC.J4TreeN.tabs (rec7900 j)

set_option maxRecDepth 400000

#kc_each j4col7900_ 0 442

#kc_forall_tree j4col7900_all (fun j => j4col7900_ j = true) 442 CFSG.KC.J4TreeCol.j4col7900_

end CFSG.KC.J4TreeCol
