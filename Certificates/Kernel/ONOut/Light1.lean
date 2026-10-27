module

import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.ONOut.Data1
public import Certificates.Data.Kernel.Spor.WordProgW

public section

set_option maxRecDepth 400000

namespace CFSG.KD.ONOut

open CFSG.KC.WP

theorem statesL : statesOK 8 WC PS 16 = true := by quickRfl

end CFSG.KD.ONOut

end
