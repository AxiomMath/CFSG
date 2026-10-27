module

public import Certificates.Data.Kernel.Misc.Sp8U0Cov
public import Certificates.Kernel.Misc.Sp8U0.Rec
public import Certificates.Kernel.Misc.Sp8U0.RecCov
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.Sp8U0

theorem u06_orb_ok : orbK COV = true := by quickRfl

theorem u06_cov_ok : covK REC COV = true := by quickRfl

end CFSG.KD.Sp8U0

end
