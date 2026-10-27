module

public import Certificates.Kernel.J4TreeCol.D7901
public import Certificates.Data.Kernel.J4TreeColPair
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallTree

public section

namespace CFSG.KC.J4TreeCol

@[expose] noncomputable def j4colq7901_ (p : Nat) : Bool :=
  pairsOKP colMats (rec7901 ((pit7901 p).getD 0 0)) ((pit7901 p).getD 1 0) ((pit7901 p).getD 2 0)

set_option maxRecDepth 400000

#kc_each j4colq7901_ 0 176

#kc_forall_tree j4colq7901_all (fun p => j4colq7901_ p = true) 176 CFSG.KC.J4TreeCol.j4colq7901_

end CFSG.KC.J4TreeCol
