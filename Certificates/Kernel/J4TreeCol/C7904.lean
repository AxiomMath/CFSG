module

public import Certificates.Kernel.J4TreeCol.D7904
public import Certificates.Data.Kernel.J4TreeColUnion
public import Certificates.Data.Kernel.J4TreeColCov
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KC.J4TreeCol

set_option maxRecDepth 400000

theorem j4colu7904_0 : colUnionOK CFSG.KC.J4TreeN.tabs (rec7904 0) = true := by quickRfl

theorem j4colu7904_1 : colUnionOK CFSG.KC.J4TreeN.tabs (rec7904 1) = true := by quickRfl

theorem j4colcov7904 : covOK rec7904 pit7904 130 2 = true := by quickRfl

end CFSG.KC.J4TreeCol
