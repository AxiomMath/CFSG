module

public import Certificates.Kernel.ONSeven.G17390Defs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.ON7GenData
public import CFSG.Sporadic.Schreier.ONCheckAuxInputs
public import Certificates.Kernel.Sporadic.ON.Seven

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ONS

open CFSG.HardMathSupport.Dickson.I271 (on7WordA on7WordB)

theorem ch17390_0 : ch17390 on7WordA on7WordB 0 = true := by quickRfl

theorem ch17390_1 : ch17390 on7WordA on7WordB 227759 = true := by quickRfl

theorem ch17390_2 : ch17390 on7WordA on7WordB 100817 = true := by quickRfl

end CertificateChecks.KernelSpor.ONS

end
