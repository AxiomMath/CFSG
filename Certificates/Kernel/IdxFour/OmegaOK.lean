module

public import Certificates.Kernel.IdxFour.OmegaData

set_option maxRecDepth 100000

public section

namespace CFSG.KD.IF4W

open CFSG.KC.IF4W

theorem cf17606tree : reachOK G D 12 2 inOmK = true := by decide +kernel

end CFSG.KD.IF4W

end
