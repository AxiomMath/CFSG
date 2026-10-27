module

public import Certificates.Data.Kernel.Spor.Mathieu
public import Certificates.Data.HZ82.Coc24
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelMathieuFam

open CFSG.KS.Mathieu CFSG.Quasithin.H.Coc24.Native

theorem lzK : mcheck 24 5 lzData = true := by quickRfl

theorem a6colK : mcheck 6 4 a6colData = true := by quickRfl

end CertificateChecks.KernelMathieuFam

end
