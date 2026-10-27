module

public import Certificates.Data.Kernel.Spor.Mathieu
public import Certificates.Data.HZ82.Code22
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelMathieuFam

open CFSG.KS.Mathieu CFSG.Quasithin.H.Code22.Native

theorem l22K : mcheck 24 5 l22Data = true := by quickRfl

end CertificateChecks.KernelMathieuFam

end
