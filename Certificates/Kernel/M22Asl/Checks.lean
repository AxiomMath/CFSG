module

public import Certificates.Data.Kernel.LocalQT.Lat
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

public section

namespace CFSG.KD.M22Asl

open CFSG.KC.LQT.L

@[expose] noncomputable def gP : List Nat :=
  [871566820143481656512471895526432, 708779051835354109451925276931104]

@[expose] noncomputable def gS : List Nat :=
  [122024278054565565571200, 346394238371114437181700]

theorem dg : diagK 22 16 64 gP gS 960 = true := by quickRfl

end CFSG.KD.M22Asl

end
