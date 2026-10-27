module

public import Certificates.Data.Kernel.S1277K7255
public import Certificates.Kernel.S1277.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KP.C7255

open CFSG.KC.C7255 CFSG.KC.S1277ML CFSG.KD.S1277Gm

theorem stab7255 :
    allL (fun c => Nat.ble (stabK (gm6P ++ gm6P.map sigP) c) 8) [5, 10, 15] = true := by quickRfl

theorem cyc7255 : cycK = true := by quickRfl

end CFSG.KP.C7255

end
