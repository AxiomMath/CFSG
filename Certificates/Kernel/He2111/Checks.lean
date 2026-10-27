module

public import Certificates.Kernel.He2111.Data
public import Certificates.Kernel.HeOrb.Data
public import Certificates.Data.Kernel.He2111K
import Certificates.Kernel.SporSch.Ru.RowsGen

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

public section

namespace CFSG.KD.He2111

open CFSG.KC.He2111 CFSG.KD.HeOrb

@[expose] noncomputable def famBr (c : Nat) : Bool :=
  brSl (BrT.F (nat_lit 0)) (GnT.F (nat_lit 0)) (GnT.F (nat_lit 1)) PI AL BE
    (Nat.mul (nat_lit 1000) c) (nat_lit 1000)

end CFSG.KD.He2111

#kss_each CFSG.KD.He2111.Br CFSG.KD.He2111.famBr 9

end
