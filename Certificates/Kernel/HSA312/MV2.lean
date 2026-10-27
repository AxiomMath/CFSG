module

public import Certificates.Kernel.HSA312.CV2

set_option maxRecDepth 100000
set_option maxHeartbeats 0
public noncomputable section

namespace CFSG.KD.HSA312

@[expose] def v2Mul (i : Nat) : Bool :=
  CFSG.KC.HSA312.explMul 1100 11 2047 64 CFSG.Quasithin.A312Hs.hsV2Mul X2 i

end CFSG.KD.HSA312

#kss_each CFSG.KD.HSA312.MV2 CFSG.KD.HSA312.v2Mul 64

end
