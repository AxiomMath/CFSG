module

public import Certificates.Data.Kernel.GammaUStepA.Class
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000

public section

namespace CFSG.KD.GUA

open CFSG.KC.GUA

theorem cs16965_b0 : clsBlk THP CLS 0 = true := by quickRfl

theorem cs16965_b1 : clsBlk THP CLS 1 = true := by quickRfl

theorem cs16965_b2 : clsBlk THP CLS 2 = true := by quickRfl

theorem cs16965_b3 : clsBlk THP CLS 3 = true := by quickRfl

end CFSG.KD.GUA

end
