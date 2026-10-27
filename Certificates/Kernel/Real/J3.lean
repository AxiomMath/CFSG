module

public import Certificates.Kernel.J3Local.Seeds
public import Certificates.Data.Kernel.OpsReal
public import Certificates.Data.CoverBRealJ3
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelReal.J3

open CFSG.KC.OpsReal CFSG.KC.OpsK CFSG.SectionRank.QTK.CoverB CertificateChecks.KernelJ3L

theorem real_K : realN (opsF2K 80) JA.M JB.M j3Real = true := by quickRfl

end CertificateChecks.KernelReal.J3

end
