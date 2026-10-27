module

public import Certificates.Data.Kernel.SmithD6.E4f7K
import all Certificates.Data.SmithD6Model

set_option maxRecDepth 100000

public section

namespace CertificateChecks.SmithD6E4f7

open CFSG.KD.SmithD6E4

theorem e4_head : e4HeadOK = true := by decide +kernel

theorem e4_all : e4AllOK = true := by decide +kernel

end CertificateChecks.SmithD6E4f7

end
