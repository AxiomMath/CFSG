module

public import Certificates.Kernel.FrameWhole.Data
public import Certificates.Kernel.FrameE78.Data
public import Certificates.Data.Kernel.FrameWholeK
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CFSG.KD.FrameWhole

open CFSG.KC.Enum CFSG.KC.FrameE78 CFSG.KC.FrameWhole CFSG.KD.FrameE78

theorem ch709590r6 : bAnd(rootOK 6 C6 36 RP6, bAnd(simpleOK 6 RP6, bAnd(closOK 6 36 RP6 CL6,
    bAnd(parOK 6 36 CL6 PT6, distOK 36 RP6)))) = true := by quickRfl

theorem ch709590u6 : unifK 6 36 RP6 (fullM 36) 36 20 = true := by quickRfl

theorem ch709590u7 : unifK 7 63 RP7 (fullM 63) 63 32 = true := by quickRfl

theorem ch709590u8 : unifK 8 120 RP8 (fullM 120) 120 56 = true := by quickRfl

theorem ch709590k6 : connK 6 36 RP6 LV6 = true := by quickRfl

theorem ch709590k7 : connK 7 63 RP7 LV7 = true := by quickRfl

theorem ch709590k8 : connK 8 120 RP8 LV8 = true := by quickRfl

end CFSG.KD.FrameWhole

end
