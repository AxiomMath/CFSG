module

public import Certificates.Kernel.Sporadic.Fi24G2e.Data
public import Certificates.Kernel.SporSch.Ru.RowsGen

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

public noncomputable section

namespace CFSG.KD.Fi24G2e

@[expose] def vldC (k : Nat) : Bool := CFSG.KD.BrFi24.VLD (BX k)

end CFSG.KD.Fi24G2e

#kss_each CFSG.KD.Fi24G2e.BV CFSG.KD.Fi24G2e.vldC 19

end
