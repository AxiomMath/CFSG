module

public import Certificates.Data.Kernel.Fi24Pkg.Defs
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public section

namespace CFSG.KD.Fi24Pkg

theorem fi24WordsOK_ok : fi24WordsOK () = true := by
  quickRfl

theorem fi24NineOK_ok : fi24NineOK xT yT = true := by
  quickRfl

theorem fi24ThreeOK_ok : fi24ThreeOK aT gT = true := by
  quickRfl

end CFSG.KD.Fi24Pkg
