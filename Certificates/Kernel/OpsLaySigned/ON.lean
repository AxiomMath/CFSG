module

public import Certificates.Kernel.FusLay.ON
public import Certificates.Data.Kernel.OpsLaySigned
public import Certificates.Data.CoverBSignedON
public import Certificates.Data.SporadicTwoCover
import all CFSG.Blueprint.NativeSporadic

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelOpsLaySigned.ON

open CFSG.KC.OpsLaySigned CFSG.SectionRank.QTK.CoverB
  CFSG.RankThree.PartTwo.Sec4.Census.SporadicTwoCover.Native
open CertificateChecks.KernelFusLay.ON

theorem signed7261_seedA : onSigned.base.seedA = String.ofList LA := LA_eq

theorem signed7261_seedB : onSigned.base.seedB = String.ofList LB := LB_eq

theorem e8_8094_seedA : onE8Data.seedA = String.ofList LA := LA_eq

theorem e8_8094_seedB : onE8Data.seedB = String.ofList LB := LB_eq

theorem signed7261_K : signedK lay A B onSigned = true := by decide +kernel

theorem e8_8094_K : e8K3 lay A B onE8Data = true := by decide +kernel

end CertificateChecks.KernelOpsLaySigned.ON

end
