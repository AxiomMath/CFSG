module

public import Certificates.Kernel.J4TreeCol.D7901
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallTree

public section

namespace CFSG.KC.J4TreeCol

@[expose] noncomputable def j4col7901_ (j : Nat) : Bool :=
  colNodeOK colMats CFSG.KC.J4TreeN.tabs (rec7901 j)

set_option maxRecDepth 400000

#kc_each j4col7901_ 0 365

#kc_forall_tree j4col7901_all (fun j => j4col7901_ j = true) 365 CFSG.KC.J4TreeCol.j4col7901_

end CFSG.KC.J4TreeCol
