module

public import Certificates.Kernel.Sporadic.OddCore.SuzBtD
public import Certificates.Kernel.Sporadic.OddCore.SuzBtND
public import Certificates.Data.Kernel.Spor.BTupN
public import Certificates.Data.Kernel.Spor.Chain
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.SuzBtNC

open CFSG.KC.Enum CFSG.KS CFSG.KS.BTup CertificateChecks.KernelSpor

theorem kCj : allN 4 (fun j => allN 8 (fun l => btCjK 11 (mask 11) 3 33 (mask 33) SuzBtM1.cnt
    SuzBtM1.K SuzBtM1.B (SuzBtCL1.G j) (SuzBtM1.G l))) = true := by quickRfl

end CertificateChecks.KernelSpor.SuzBtNC

end
