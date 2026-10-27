module

public import Certificates.Kernel.Q8Wit.J3EnumK
public import Certificates.Kernel.Q8Wit.J3Data
public import Certificates.Data.Kernel.Q8WitP2
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelQ8W.J3

open CFSG.KC.Q8Wit

theorem sqsJ : sqsK 6156 13 J3Q.N J3Q.T SQ = true := by quickRfl

end CertificateChecks.KernelQ8W.J3

end
