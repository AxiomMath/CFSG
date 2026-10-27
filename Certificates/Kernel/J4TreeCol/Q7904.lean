module

public import Certificates.Kernel.J4TreeCol.D7904
public import Certificates.Data.Kernel.J4TreeColPair
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallTree

public section

namespace CFSG.KC.J4TreeCol

@[expose] noncomputable def j4colq7904_ (p : Nat) : Bool :=
  pairsOKP colMats (rec7904 ((pit7904 p).getD 0 0)) ((pit7904 p).getD 1 0) ((pit7904 p).getD 2 0)

set_option maxRecDepth 400000

#kc_each j4colq7904_ 0 130

#kc_forall_tree j4colq7904_all (fun p => j4colq7904_ p = true) 130 CFSG.KC.J4TreeCol.j4colq7904_

end CFSG.KC.J4TreeCol
