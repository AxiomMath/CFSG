module

public import Certificates.Kernel.LocalComp.HeFix
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeGSCertInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.HeGSX

open CFSG.KC.Enum CFSG.KS CFSG.KC.PermTool CFSG.ComponentClassification.GrSLit.HeldFix
open CFSG.ComponentClassification.GrSLit.HeGS CertificateChecks.KernelLC.HeFix

theorem kX12 : Nat.beq (wordTabK 8330 14 PC1 (hfRep 12 heGSXWord)) (pidn 8330 14) = true := by
  quickRfl

end CertificateChecks.KernelLC.HeGSX

end
