module

public import Certificates.Kernel.J4TreeCol.D7902
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallTree

public section

namespace CFSG.KC.J4TreeCol

@[expose] noncomputable def j4col7902_ (j : Nat) : Bool :=
  colNodeOK colMats CFSG.KC.J4TreeN.tabs (rec7902 j)

set_option maxRecDepth 400000

#kc_each j4col7902_ 0 261

#kc_forall_tree j4col7902_all (fun j => j4col7902_ j = true) 261 CFSG.KC.J4TreeCol.j4col7902_

end CFSG.KC.J4TreeCol
