module

public import Certificates.Kernel.FusLay.McL
public import Certificates.Data.Kernel.OpsLaySigned
public import Certificates.Data.CoverBSignedMcL
import all CFSG.Blueprint.NativeSporadic

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelOpsLaySigned.McL

open CFSG.KC.OpsLaySigned CFSG.SectionRank.QTK.CoverB
open CertificateChecks.KernelFusLay.McL

theorem signed7263_seedA : mclSigned.base.seedA = String.ofList LA := LA_eq

theorem signed7263_seedB : mclSigned.base.seedB = String.ofList LB := LB_eq

theorem signed7263_K : signedK lay A B mclSigned = true := by decide +kernel

end CertificateChecks.KernelOpsLaySigned.McL

end
