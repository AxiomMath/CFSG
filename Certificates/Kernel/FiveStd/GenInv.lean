module

public import Certificates.Kernel.FiveStd.ClsData
public import Certificates.Data.Kernel.FiveStdKOrb
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.FiveStd

open CFSG.KC.FiveStdK

theorem gi_valid : allN 2 (fun l => validK (f20 GI l)) = true := by quickRfl

end CertificateChecks.FiveStd

end
