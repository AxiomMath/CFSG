module

public import Certificates.Data.Kernel.SmithD6.NcK

set_option maxRecDepth 100000

public section

namespace CertificateChecks.SmithD6Nc

open CFSG.KD.SmithD6Nc

theorem nc_ok : ncOK = true := by decide +kernel

end CertificateChecks.SmithD6Nc

end
