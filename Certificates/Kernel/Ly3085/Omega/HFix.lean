module

public import Certificates.Kernel.Ly3085.Omega.Base
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KD.LyOm

@[expose] noncomputable def hGens : List (Nat × List Nat) :=
  [(BE3, WH3_0), (BE3, WH3_1), (BE3, WH3_2), (BE4, WH4_0), (BE4, WH4_1), (BE4, WH4_2),
    (BE4, WH4_3)]

theorem fwh : hGens.all (fun p => fixBeta p.1 p.2) = true := by quickRfl

end CFSG.KD.LyOm

end
