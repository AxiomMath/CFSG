module

public import Certificates.Data.Kernel.G2Three.Sec1T3B
public import Certificates.Kernel.G2Three.Sec1T3Data
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.G2Three.Sec1T3

theorem s3_rowLt : (rowsLtK 408 LO0 && rowsLtK 408 LO1 && rowsLtK 408 LO2 && rowsLtK 408 LO3 &&
    rowsLtK 408 LO4 && rowsLtK 408 LO5 && rowsLtK 408 LO6 && rowsLtK 408 LO7) = true := by
  quickRfl

end CFSG.KD.G2Three.Sec1T3

end
