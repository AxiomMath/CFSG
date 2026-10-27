module

public import Certificates.Data.Kernel.Spor.Mathieu
public import Certificates.Data.HZ82.L34
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelMathieuFam

open CFSG.KS.Mathieu CFSG.Quasithin.H.L34Z.Native

theorem l34K : mcheck 512 10 l34Data = true := by quickRfl

end CertificateChecks.KernelMathieuFam

end
