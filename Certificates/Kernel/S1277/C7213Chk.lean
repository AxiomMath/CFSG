module

public import Certificates.Data.Kernel.S1277K7213
public import Certificates.Kernel.S1277.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KP.C7213

open CFSG.KC.C7213 CFSG.KC.S1277ML CFSG.KD.S1277Gm

theorem len7213 : Nat.beq gmIdx.length 1080 = true := by quickRfl

theorem chk7213_ok : chk7213 gmIdx = true := by quickRfl

theorem neg7213a : notB (chk7213 (gmIdx.set 500 0)) = true := by quickRfl

theorem neg7213b : notB (chk7213 gmIdx.tail) = true := by quickRfl

end CFSG.KP.C7213

end
