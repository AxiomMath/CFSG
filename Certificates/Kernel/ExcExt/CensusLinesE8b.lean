module

public import Certificates.Data.Kernel.ExcExt.CensusTwin
public import Certificates.Kernel.ExcExt.Data
public import Certificates.Kernel.ExcExt.CensusData
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.ExcExtK

set_option maxRecDepth 100000

theorem ch712511l5_4 : scanLineCK D.T5 C5.L4 = true := by quickRfl
theorem ch712511l5_14 : scanLineCK D.T5 C5.L14 = true := by quickRfl

end CFSG.ExcExtK

end
