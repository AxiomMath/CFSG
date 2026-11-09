module

public import Certificates.Kernel.Sporadic.OddCore.Suz2308K
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.OddCore.S2308

open CFSG.KC.Enum CFSG.KS CFSG.KS.Row CFSG.KS.Raw CertificateChecks.KernelSpor

theorem lperm : allN 14 (fun j => permOK 280 9 (mask 9) (280 * 9) (S2308LC.S j) (S2308LC.SI j)) =
    true := by quickRfl

end CertificateChecks.KernelSpor.OddCore.S2308

end
