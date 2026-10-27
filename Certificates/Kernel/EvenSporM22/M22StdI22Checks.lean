module

public import Certificates.Data.Kernel.EvenSporM22.M22StdDefs
public import Certificates.Kernel.LocalQT.Cov.C4101
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CFSG.KD.M22S

open CFSG.KC.M22S CFSG.KD.LQT.C4101

theorem kI22 : i22K 228952723507329932679484465855724 81506110577382089737470578414133 CT.chars hWK =
    true := by quickRfl

end CFSG.KD.M22S

end
