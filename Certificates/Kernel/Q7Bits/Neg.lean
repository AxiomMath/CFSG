module

public import Certificates.Kernel.Q7Bits.Data
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CFSG.KD.Q7Bits

open CFSG.Certificates.Kernel.Q7Bits CFSG.ClassicalInvolution.PhanB3.S.Std.Q7

theorem neg0 : rowCheck q7RepsData[0]! (rt.getD 0 0) ((lv.getD 0 []).take 2) = false := by
  decide +kernel

theorem neg1 : rowCheck q7RepsData[0]! (rt.getD 0 0) (lv.getD 1 []) = false := by
  decide +kernel

end CFSG.KD.Q7Bits
