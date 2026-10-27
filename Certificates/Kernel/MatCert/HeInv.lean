module

public import Certificates.Kernel.MatCert.Fp
public import Certificates.Data.Kernel.OpsCubN
public import Certificates.Data.SmithB45ExcHe
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMC

open CFSG.KC.OpsCubN CFSG.KC.OpsK CFSG.SectionRank.Native CFSG.Quasithin.B45Exc

theorem heInv_K : forceB (payHe HeS1.chars) (fun A => forceB (payHe HeS2.chars) fun B =>
    vldHe A && vldHe B && cubicN O7 A B heInvData) = true := by
  quickRfl

end CertificateChecks.KernelMC

end
