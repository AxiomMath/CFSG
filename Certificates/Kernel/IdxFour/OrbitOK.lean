module

public import Certificates.Kernel.IdxFour.OrbitData

set_option maxRecDepth 100000

public section

namespace CFSG.KD.IF4O

open CFSG.KC.IF4O

theorem cf17603tree : treeOK G D = true := by decide +kernel

end CFSG.KD.IF4O

end
