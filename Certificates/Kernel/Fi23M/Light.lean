module

import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.Fi23M.Data
public import Certificates.Data.Kernel.Spor.WordProgW

public section

set_option maxRecDepth 400000

namespace CFSG.KD.Fi23M

open CFSG.KC.WP

theorem statesL : statesOK 2 WC PS 10 = true := by quickRfl

theorem relsL : relProgsOK 2 10 PR 5 = true := by quickRfl

end CFSG.KD.Fi23M

end
