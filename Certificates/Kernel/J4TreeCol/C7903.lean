module

public import Certificates.Kernel.J4TreeCol.D7903
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallTree

public section

namespace CFSG.KC.J4TreeCol

@[expose] noncomputable def j4col7903_ (j : Nat) : Bool :=
  colNodeOK colMats CFSG.KC.J4TreeN.tabs (rec7903 j)

set_option maxRecDepth 400000

#kc_each j4col7903_ 0 194

#kc_forall_tree j4col7903_all (fun j => j4col7903_ j = true) 194 CFSG.KC.J4TreeCol.j4col7903_

end CFSG.KC.J4TreeCol
