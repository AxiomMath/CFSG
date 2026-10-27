module

public import Certificates.Kernel.EvenBN.Thm49ETOData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelT49

open CFSG.KC.Enum CFSG.KS CFSG.KD.T49

theorem search43_3 : allBlk 69 (fun i3 => searchK w43 i3) 23 = true := by quickRfl

end CertificateChecks.KernelT49

end
