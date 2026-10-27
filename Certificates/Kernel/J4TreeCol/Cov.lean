module

public import Certificates.Kernel.J4TreeCol.D7900
public import Certificates.Kernel.J4TreeCol.D7901
public import Certificates.Kernel.J4TreeCol.D7902
public import Certificates.Kernel.J4TreeCol.D7903
public import Certificates.Data.Kernel.J4TreeColCov
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KC.J4TreeCol

set_option maxRecDepth 400000

theorem j4colcov7900 : covOK rec7900 pit7900 200 442 = true := by quickRfl

theorem j4colcov7901 : covOK rec7901 pit7901 176 365 = true := by quickRfl

theorem j4colcov7902 : covOK rec7902 pit7902 180 261 = true := by quickRfl

theorem j4colcov7903 : covOK rec7903 pit7903 155 194 = true := by quickRfl

end CFSG.KC.J4TreeCol
