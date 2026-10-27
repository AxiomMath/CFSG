module

public import Certificates.Data.KappaLemmaA
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelEvenBN.K561002

open Certificates.KappaLemmaA

theorem table0K : table0OK () = true := by quickRfl

theorem table1K : table1OK () = true := by quickRfl

theorem comboK : comboOK () = true := by quickRfl

end CertificateChecks.KernelEvenBN.K561002

end
