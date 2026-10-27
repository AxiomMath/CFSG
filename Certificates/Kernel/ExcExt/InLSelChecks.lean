module

public import Certificates.Data.Kernel.ExcExt.InLSelTwin
public import Certificates.Kernel.ExcExt.Data
public import Certificates.Kernel.ExcExt.InLSelData
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.ExcExtK

set_option maxRecDepth 100000

theorem ch712516l4_0 : scanLineLK D.T4 S4.Es S4.L0 = true := by quickRfl
theorem ch712516l4_1 : scanLineLK D.T4 S4.Es S4.L1 = true := by quickRfl
theorem ch712516l4_4 : scanLineLK D.T4 S4.Es S4.L4 = true := by quickRfl
theorem ch712516l4_11 : scanLineLK D.T4 S4.Es S4.L11 = true := by quickRfl
theorem ch712516l4_14 : scanLineLK D.T4 S4.Es S4.L14 = true := by quickRfl
theorem ch712516l4_416 : scanLineLK D.T4 S4.Es S4.L416 = true := by quickRfl

theorem ch712516e6 : e6AllK D.T4 S4.Es S4.Es = true := by quickRfl

theorem ch712516pr : pairRangeK D.T4 = true := by quickRfl

end CFSG.ExcExtK

end
