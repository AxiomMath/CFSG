module

public import Certificates.Kernel.J4TreeCol.D7903
public import Certificates.Data.Kernel.J4TreeColPair
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallTree

public section

namespace CFSG.KC.J4TreeCol

@[expose] noncomputable def j4colq7903_ (p : Nat) : Bool :=
  pairsOKP colMats (rec7903 ((pit7903 p).getD 0 0)) ((pit7903 p).getD 1 0) ((pit7903 p).getD 2 0)

set_option maxRecDepth 400000

#kc_each j4colq7903_ 0 155

#kc_forall_tree j4colq7903_all (fun p => j4colq7903_ p = true) 155 CFSG.KC.J4TreeCol.j4colq7903_

end CFSG.KC.J4TreeCol
