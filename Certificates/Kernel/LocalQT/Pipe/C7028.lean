module

public import Certificates.Kernel.LocalQT.Pipe.F4050
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.LQT.C4050

open CFSG.KC.LQT.S CFSG.KC.LQT.PP CFSG.QuasithinUnique.Setup.X1

@[expose] def size7028 (s : Nat) : Bool := s == 1 || s % 3 == 0

theorem ch7028 : (List.range 6).all (fun h => size7028 (popK 4725 (getK BM h))) = true := by
  quickRfl

end CFSG.KD.LQT.C4050

end
