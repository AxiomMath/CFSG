module

public import Certificates.Data.Kernel.S23Unitary
public import Certificates.Kernel.TwoE6.UnitaryData
public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.Stroth23UnitaryInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelTwoE6

open CFSG.KC.S23U CFSG.KLie.CT CFSG.EvenSmallLie.TwoE6 CFSG.Monster.B.TwoA.Unitary

theorem kBind3177 : andB (bindW G20 20 20 17 u20Gens) (andB (bindW B6 12 6 17 b6MatArr)
    (bindW NP 12 6 6 nuPowArr)) = true := by quickRfl

theorem kG20 : G20 < 2 ^ 6800 := by decide +kernel

theorem kGeom : geomZero G20 nuWord = true := by quickRfl
theorem kPows : powsOK B6 NP = true := by quickRfl
theorem kCyc : cycOK NP CV = true := by quickRfl
theorem kScal : scalOK NP = true := by quickRfl

end CertificateChecks.KernelTwoE6

end
